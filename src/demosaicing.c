/*
   dcraw.c -- Dave Coffin's raw photo decoder
   Copyright 1997-2016 by Dave Coffin, dcoffin a cybercom o net
   This is a command-line ANSI C program to convert raw photos from
   any digital camera on any computer running any operating system.
   No license is required to download and use dcraw.c.  However,
   to lawfully redistribute dcraw, you must either (a) offer, at
   no extra charge, full source code* for all executable files
   containing RESTRICTED functions, (b) distribute this code under
   the GPL Version 2 or later, (c) remove all RESTRICTED functions,
   re-implement them, or copy them from an earlier, unrestricted
   Revision of dcraw.c, or (d) purchase a license from the author.
   The functions that process Foveon images have been RESTRICTED
   since Revision 1.237.  All other code remains free for all uses.
   *If you have not modified dcraw.c in any way, a link to my
   homepage qualifies as "full source code".
   $Revision: 1.477 $
   $Date: 2016/05/10 21:30:43 $
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <float.h>
#include <limits.h>
#include <math.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/types.h>

#if defined(DJGPP) || defined(__MINGW32__)
#define fseeko fseek
#define ftello ftell
#else
#define fgetc getc_unlocked
#endif
#ifdef __CYGWIN__
#include <io.h>
#endif
#ifdef WIN32
#include <sys/utime.h>
#include <winsock2.h>
#pragma comment(lib, "ws2_32.lib")
#define snprintf _snprintf
#define strcasecmp stricmp
#define strncasecmp strnicmp
typedef __int64 INT64;
typedef unsigned __int64 UINT64;
#else
#include <unistd.h>
#include <utime.h>
#include <netinet/in.h>
typedef long long INT64;
typedef unsigned long long UINT64;
#endif
extern int demo (const char *fp);

#ifdef NODEPS
#define NO_JASPER
#define NO_JPEG
#define NO_LCMS
#endif
#ifndef NO_JASPER
#include <jasper/jasper.h>	/* Decode Red camera movies */
#endif
#ifndef NO_JPEG
#include <jpeglib.h>		/* Decode compressed Kodak DC120 photos */
#endif				/* and Adobe Lossy DNGs */
#ifndef NO_LCMS
#include <lcms2.h>		/* Support color profiles */
#endif
#ifdef LOCALEDIR
#include <libintl.h>
#define _(String) gettext(String)
#else
#define _(String) (String)
#endif

#if !defined(uchar)
#define uchar unsigned char
#endif
#if !defined(ushort)
#define ushort unsigned short
#endif

/*
   All global variables are defined here, and all functions that
   access them are prefixed with "CLASS".  Note that a thread-safe
   C++ class cannot have non-const static local variables.
 */
FILE *ifp, *ofp;
short order;
const char *ifname;
char *meta_data, xtrans[6][6], xtrans_abs[6][6];
char cdesc[5], desc[512], make[64], model[64], model2[64], artist[64];
float flash_used, canon_ev, iso_speed, shutter, aperture, focal_len;
time_t timestamp;
off_t strip_offset, data_offset;
off_t thumb_offset, meta_offset, profile_offset;
unsigned shot_order, kodak_cbpp, exif_cfa, unique_id;
unsigned thumb_length, meta_length, profile_length;
unsigned thumb_misc, *oprof, fuji_layout, shot_select=0, multi_out=0;
unsigned black, maximum, mix_green, raw_color, zero_is_bad;
unsigned zero_after_ff, is_raw, dng_version, is_foveon, data_error;
unsigned tile_width, tile_length, gpsdata[32], load_flags;
unsigned flip, tiff_flip, filters, colors;
ushort raw_height, raw_width, raw_stride=0, height, width, top_margin, left_margin;
ushort shrink, iheight, iwidth, thumb_width, thumb_height;
ushort *raw_image, (*image)[4], cblack[4102];
ushort white[8][8], curve[0x10000], cr2_slice[3], sraw_mul[4];
double pixel_aspect, aber[4]={1,1,1,1}, gamm[6]={ 0.45,4.5,0,0,0,0 };
float bright=1, user_mul[4]={0,0,0,0}, threshold=0;
int mask[8][4];
int half_size=0, four_color_rgb=0, document_mode=0, highlight=0;
int verbose=0, use_auto_wb=0, use_camera_wb=0, use_camera_matrix=1;
int output_color=1, output_bps=8, output_tiff=0, med_passes=0;
int no_auto_bright=0;
unsigned greybox[4] = { 0, 0, UINT_MAX, UINT_MAX };
float cam_mul[4], pre_mul[4], cmatrix[3][4], rgb_cam[3][4];
const double xyz_rgb[3][3] = {			/* XYZ from RGB */
  { 0.412453, 0.357580, 0.180423 },
  { 0.212671, 0.715160, 0.072169 },
  { 0.019334, 0.119193, 0.950227 } };
const float d65_white[3] = { 0.950456, 1, 1.088754 };
int histogram[4][0x2000];
void (*write_thumb)(), (*write_fun)();
void (*load_raw)(), (*thumb_load_raw)();
jmp_buf failure;

struct ph1 {
  int format, key_off, tag_21a;
  int black, split_col, black_col, split_row, black_row;
  float tag_210;
} ph1;

#define CLASS

#define FORC(cnt) for (c=0; c < cnt; c++)
#define FORC2 FORC(2)
#define FORC3 FORC(3)
#define FORC4 FORC(4)
#define FORCC FORC(colors)

#define SQR(x) ((x)*(x))
#define ABS(x) (((int)(x) ^ ((int)(x) >> 31)) - ((int)(x) >> 31))
#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define MAX(a,b) ((a) > (b) ? (a) : (b))
#define LIM(x,min,max) MAX(min,MIN(x,max))
#define ULIM(x,y,z) ((y) < (z) ? LIM(x,y,z) : LIM(x,z,y))
#define CLIP(x) LIM((int)(x),0,65535)
#define SWAP(a,b) { a=a+b; b=a-b; a=a-b; }

/*
   In order to inline this calculation, I make the risky
   assumption that all filter patterns can be described
   by a repeating pattern of eight rows and two columns

   Do not use the FC or BAYER macros with the Leaf CatchLight,
   because its pattern is 16x16, not 2x8.

   Return values are either 0/1/2/3 = G/M/C/Y or 0/1/2/3 = R/G1/B/G2

	PowerShot 600	PowerShot A50	PowerShot Pro70	Pro90 & G1
	0xe1e4e1e4:	0x1b4e4b1e:	0x1e4b4e1b:	0xb4b4b4b4:

	  0 1 2 3 4 5	  0 1 2 3 4 5	  0 1 2 3 4 5	  0 1 2 3 4 5
	0 G M G M G M	0 C Y C Y C Y	0 Y C Y C Y C	0 G M G M G M
	1 C Y C Y C Y	1 M G M G M G	1 M G M G M G	1 Y C Y C Y C
	2 M G M G M G	2 Y C Y C Y C	2 C Y C Y C Y
	3 C Y C Y C Y	3 G M G M G M	3 G M G M G M
			4 C Y C Y C Y	4 Y C Y C Y C
	PowerShot A5	5 G M G M G M	5 G M G M G M
	0x1e4e1e4e:	6 Y C Y C Y C	6 C Y C Y C Y
			7 M G M G M G	7 M G M G M G
	  0 1 2 3 4 5
	0 C Y C Y C Y
	1 G M G M G M
	2 C Y C Y C Y
	3 M G M G M G

   All RGB cameras use one of these Bayer grids:

	0x16161616:	0x61616161:	0x49494949:	0x94949494:

	  0 1 2 3 4 5	  0 1 2 3 4 5	  0 1 2 3 4 5	  0 1 2 3 4 5
	0 B G B G B G	0 G R G R G R	0 G B G B G B	0 R G R G R G
	1 G R G R G R	1 B G B G B G	1 R G R G R G	1 G B G B G B
	2 B G B G B G	2 G R G R G R	2 G B G B G B	2 R G R G R G
	3 G R G R G R	3 B G B G B G	3 R G R G R G	3 G B G B G B
 */

#define RAW(row,col) \
	raw_image[(row)*raw_width+(col)]

#define FC(row,col) \
	(filters >> ((((row) << 1 & 14) + ((col) & 1)) << 1) & 3)

#define BAYER(row,col) \
	image[((row) >> shrink)*iwidth + ((col) >> shrink)][FC(row,col)]

#define BAYER2(row,col) \
	image[((row) >> shrink)*iwidth + ((col) >> shrink)][fcol(row,col)]

int CLASS fcol (int row, int col)
{
  static const char filter[16][16] =
  { { 2,1,1,3,2,3,2,0,3,2,3,0,1,2,1,0 },
    { 0,3,0,2,0,1,3,1,0,1,1,2,0,3,3,2 },
    { 2,3,3,2,3,1,1,3,3,1,2,1,2,0,0,3 },
    { 0,1,0,1,0,2,0,2,2,0,3,0,1,3,2,1 },
    { 3,1,1,2,0,1,0,2,1,3,1,3,0,1,3,0 },
    { 2,0,0,3,3,2,3,1,2,0,2,0,3,2,2,1 },
    { 2,3,3,1,2,1,2,1,2,1,1,2,3,0,0,1 },
    { 1,0,0,2,3,0,0,3,0,3,0,3,2,1,2,3 },
    { 2,3,3,1,1,2,1,0,3,2,3,0,2,3,1,3 },
    { 1,0,2,0,3,0,3,2,0,1,1,2,0,1,0,2 },
    { 0,1,1,3,3,2,2,1,1,3,3,0,2,1,3,2 },
    { 2,3,2,0,0,1,3,0,2,0,1,2,3,0,1,0 },
    { 1,3,1,2,3,2,3,2,0,2,0,1,1,0,3,0 },
    { 0,2,0,3,1,0,0,1,1,3,3,2,3,2,2,1 },
    { 2,1,3,2,3,1,2,1,0,3,0,2,0,2,0,2 },
    { 0,3,1,0,0,2,0,3,2,1,3,1,1,3,1,3 } };

  if (filters == 1) return filter[(row+top_margin)&15][(col+left_margin)&15];
  if (filters == 9) return xtrans[(row+6) % 6][(col+6) % 6];
  return FC(row,col);
}

#ifndef __GLIBC__
char *my_memmem (char *haystack, size_t haystacklen,
	      char *needle, size_t needlelen)
{
  char *c;
  for (c = haystack; c <= haystack + haystacklen - needlelen; c++)
    if (!memcmp (c, needle, needlelen))
      return c;
  return 0;
}
#define memmem my_memmem
char *my_strcasestr (char *haystack, const char *needle)
{
  char *c;
  for (c = haystack; *c; c++)
    if (!strncasecmp(c, needle, strlen(needle)))
      return c;
  return 0;
}
#define strcasestr my_strcasestr
#endif

void CLASS merror (void *ptr, const char *where)
{
  if (ptr) return;
  fprintf (stderr,_("%s: Out of memory in %s\n"), ifname, where);
  longjmp (failure, 1);
}

void CLASS derror()
{
  if (!data_error) {
    fprintf (stderr, "%s: ", ifname);
    if (feof(ifp))
      fprintf (stderr,_("Unexpected end of file\n"));
    else
      fprintf (stderr,_("Corrupt data near 0x%llx\n"), (INT64) ftello(ifp));
  }
  data_error++;
}

ushort CLASS sget2 (uchar *s)
{
  if (order == 0x4949)		/* "II" means little-endian */
    return s[0] | s[1] << 8;
  else				/* "MM" means big-endian */
    return s[0] << 8 | s[1];
}

ushort CLASS get2()
{
  uchar str[2] = { 0xff,0xff };
  fread (str, 1, 2, ifp);
  return sget2(str);
}

unsigned CLASS sget4 (uchar *s)
{
  if (order == 0x4949)
    return s[0] | s[1] << 8 | s[2] << 16 | s[3] << 24;
  else
    return s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3];
}
#define sget4(s) sget4((uchar *)s)

unsigned CLASS get4()
{
  uchar str[4] = { 0xff,0xff,0xff,0xff };
  fread (str, 1, 4, ifp);
  return sget4(str);
}

float CLASS int_to_float (int i)
{
  union { int i; float f; } u;
  u.i = i;
  return u.f;
}

double CLASS getreal (int type)
{
  union { char c[8]; double d; } u;
  int i, rev;

  switch (type) {
    case 3: return (unsigned short) get2();
    case 4: return (unsigned int) get4();
    case 5:  u.d = (unsigned int) get4();
      return u.d / (unsigned int) get4();
    case 8: return (signed short) get2();
    case 9: return (signed int) get4();
    case 10: u.d = (signed int) get4();
      return u.d / (signed int) get4();
    case 11: return int_to_float (get4());
    case 12:
      rev = 7 * ((order == 0x4949) == (ntohs(0x1234) == 0x1234));
      for (i=0; i < 8; i++)
	u.c[i ^ rev] = fgetc(ifp);
      return u.d;
    default: return fgetc(ifp);
  }
}

void CLASS read_shorts (ushort *pixel, int count)
{
  if (fread (pixel, 2, count, ifp) < count) derror();
  if ((order == 0x4949) == (ntohs(0x1234) == 0x1234))
    swab (pixel, pixel, count*2);
}

void CLASS cubic_spline (const int *x_, const int *y_, const int len)
{
  float **A, *b, *c, *d, *x, *y;
  int i, j;

  A = (float **) calloc (((2*len + 4)*sizeof **A + sizeof *A), 2*len);
  if (!A) return;
  A[0] = (float *) (A + 2*len);
  for (i = 1; i < 2*len; i++)
    A[i] = A[0] + 2*len*i;
  y = len + (x = i + (d = i + (c = i + (b = A[0] + i*i))));
  for (i = 0; i < len; i++) {
    x[i] = x_[i] / 65535.0;
    y[i] = y_[i] / 65535.0;
  }
  for (i = len-1; i > 0; i--) {
    b[i] = (y[i] - y[i-1]) / (x[i] - x[i-1]);
    d[i-1] = x[i] - x[i-1];
  }
  for (i = 1; i < len-1; i++) {
    A[i][i] = 2 * (d[i-1] + d[i]);
    if (i > 1) {
      A[i][i-1] = d[i-1];
      A[i-1][i] = d[i-1];
    }
    A[i][len-1] = 6 * (b[i+1] - b[i]);
  }
  for(i = 1; i < len-2; i++) {
    float v = A[i+1][i] / A[i][i];
    for(j = 1; j <= len-1; j++)
      A[i+1][j] -= v * A[i][j];
  }
  for(i = len-2; i > 0; i--) {
    float acc = 0;
    for(j = i; j <= len-2; j++)
      acc += A[i][j]*c[j];
    c[i] = (A[i][len-1] - acc) / A[i][i];
  }
  for (i = 0; i < 0x10000; i++) {
    float x_out = (float)(i / 65535.0);
    float y_out = 0;
    for (j = 0; j < len-1; j++) {
      if (x[j] <= x_out && x_out <= x[j+1]) {
	float v = x_out - x[j];
	y_out = y[j] +
	  ((y[j+1] - y[j]) / d[j] - (2 * d[j] * c[j] + c[j+1] * d[j])/6) * v
	   + (c[j] * 0.5) * v*v + ((c[j+1] - c[j]) / (6 * d[j])) * v*v*v;
      }
    }
    curve[i] = y_out < 0.0 ? 0 : (y_out >= 1.0 ? 65535 :
		(ushort)(y_out * 65535.0 + 0.5));
  }
  free (A);
}

unsigned CLASS getbithuff (int nbits, ushort *huff)
{
  static unsigned bitbuf=0;
  static int vbits=0, reset=0;
  unsigned c;

  if (nbits > 25) return 0;
  if (nbits < 0)
    return bitbuf = vbits = reset = 0;
  if (nbits == 0 || vbits < 0) return 0;
  while (!reset && vbits < nbits && (c = fgetc(ifp)) != EOF &&
    !(reset = zero_after_ff && c == 0xff && fgetc(ifp))) {
    bitbuf = (bitbuf << 8) + (uchar) c;
    vbits += 8;
  }
  c = bitbuf << (32-vbits) >> (32-nbits);
  if (huff) {
    vbits -= huff[c] >> 8;
    c = (uchar) huff[c];
  } else
    vbits -= nbits;
  if (vbits < 0) derror();
  return c;
}

#define getbits(n) getbithuff(n,0)
#define gethuff(h) getbithuff(*h,h+1)

/*
   Construct a decode tree according the specification in *source.
   The first 16 bytes specify how many codes should be 1-bit, 2-bit
   3-bit, etc.  Bytes after that are the leaf values.

   For example, if the source is

    { 0,1,4,2,3,1,2,0,0,0,0,0,0,0,0,0,
      0x04,0x03,0x05,0x06,0x02,0x07,0x01,0x08,0x09,0x00,0x0a,0x0b,0xff  },

   then the code is

	00		0x04
	010		0x03
	011		0x05
	100		0x06
	101		0x02
	1100		0x07
	1101		0x01
	11100		0x08
	11101		0x09
	11110		0x00
	111110		0x0a
	1111110		0x0b
	1111111		0xff
 */
ushort * CLASS make_decoder_ref (const uchar **source)
{
  int max, len, h, i, j;
  const uchar *count;
  ushort *huff;

  count = (*source += 16) - 17;
  for (max=16; max && !count[max]; max--);
  huff = (ushort *) calloc (1 + (1 << max), sizeof *huff);
  merror (huff, "make_decoder()");
  huff[0] = max;
  for (h=len=1; len <= max; len++)
    for (i=0; i < count[len]; i++, ++*source)
      for (j=0; j < 1 << (max-len); j++)
	if (h <= 1 << max)
	  huff[h++] = len << 8 | **source;
  return huff;
}

struct jhead {
  int algo, bits, high, wide, clrs, sraw, psv, restart, vpred[6];
  ushort quant[64], idct[64], *huff[20], *free[20], *row;
};

int CLASS ljpeg_start (struct jhead *jh, int info_only)
{
  ushort c, tag, len;
  uchar data[0x10000];
  const uchar *dp;

  memset (jh, 0, sizeof *jh);
  jh->restart = INT_MAX;
  if ((fgetc(ifp),fgetc(ifp)) != 0xd8) return 0;
  do {
    if (!fread (data, 2, 2, ifp)) return 0;
    tag =  data[0] << 8 | data[1];
    len = (data[2] << 8 | data[3]) - 2;
    if (tag <= 0xff00) return 0;
    fread (data, 1, len, ifp);
    switch (tag) {
      case 0xffc3:
	jh->sraw = ((data[7] >> 4) * (data[7] & 15) - 1) & 3;
      case 0xffc1:
      case 0xffc0:
	jh->algo = tag & 0xff;
	jh->bits = data[0];
	jh->high = data[1] << 8 | data[2];
	jh->wide = data[3] << 8 | data[4];
	jh->clrs = data[5] + jh->sraw;
	if (len == 9 && !dng_version) getc(ifp);
	break;
      case 0xffc4:
	if (info_only) break;
	for (dp = data; dp < data+len && !((c = *dp++) & -20); )
	  jh->free[c] = jh->huff[c] = make_decoder_ref (&dp);
	break;
      case 0xffda:
	jh->psv = data[1+data[0]*2];
	jh->bits -= data[3+data[0]*2] & 15;
	break;
      case 0xffdb:
	FORC(64) jh->quant[c] = data[c*2+1] << 8 | data[c*2+2];
	break;
      case 0xffdd:
	jh->restart = data[0] << 8 | data[1];
    }
  } while (tag != 0xffda);
  if (jh->bits > 16 || jh->clrs > 6 ||
     !jh->bits || !jh->high || !jh->wide || !jh->clrs) return 0;
  if (info_only) return 1;
  if (!jh->huff[0]) return 0;
  FORC(19) if (!jh->huff[c+1]) jh->huff[c+1] = jh->huff[c];
  if (jh->sraw) {
    FORC(4)        jh->huff[2+c] = jh->huff[1];
    FORC(jh->sraw) jh->huff[1+c] = jh->huff[0];
  }
  jh->row = (ushort *) calloc (jh->wide*jh->clrs, 4);
  merror (jh->row, "ljpeg_start()");
  return zero_after_ff = 1;
}

int CLASS raw (unsigned row, unsigned col)
{
  return (row < raw_height && col < raw_width) ? RAW(row,col) : 0;
}

void CLASS phase_one_flat_field (int is_float, int nc)
{
  ushort head[8];
  unsigned wide, high, y, x, c, rend, cend, row, col;
  float *mrow, num, mult[4];

  read_shorts (head, 8);
  if (head[2] * head[3] * head[4] * head[5] == 0) return;
  wide = head[2] / head[4] + (head[2] % head[4] != 0);
  high = head[3] / head[5] + (head[3] % head[5] != 0);
  mrow = (float *) calloc (nc*wide, sizeof *mrow);
  merror (mrow, "phase_one_flat_field()");
  for (y=0; y < high; y++) {
    for (x=0; x < wide; x++)
      for (c=0; c < nc; c+=2) {
	num = is_float ? getreal(11) : get2()/32768.0;
	if (y==0) mrow[c*wide+x] = num;
	else mrow[(c+1)*wide+x] = (num - mrow[c*wide+x]) / head[5];
      }
    if (y==0) continue;
    rend = head[1] + y*head[5];
    for (row = rend-head[5];
	 row < raw_height && row < rend &&
	 row < head[1]+head[3]-head[5]; row++) {
      for (x=1; x < wide; x++) {
	for (c=0; c < nc; c+=2) {
	  mult[c] = mrow[c*wide+x-1];
	  mult[c+1] = (mrow[c*wide+x] - mult[c]) / head[4];
	}
	cend = head[0] + x*head[4];
	for (col = cend-head[4];
	     col < raw_width &&
	     col < cend && col < head[0]+head[2]-head[4]; col++) {
	  c = nc > 2 ? FC(row-top_margin,col-left_margin) : 0;
	  if (!(c & 1)) {
	    c = RAW(row,col) * mult[c];
	    RAW(row,col) = LIM(c,0,65535);
	  }
	  for (c=0; c < nc; c+=2)
	    mult[c] += mult[c+1];
	}
      }
      for (x=0; x < wide; x++)
	for (c=0; c < nc; c+=2)
	  mrow[c*wide+x] += mrow[(c+1)*wide+x];
    }
  }
  free (mrow);
}

void CLASS phase_one_correct()
{
  unsigned entries, tag, data, save, col, row, type;
  int len, i, j, k, cip, val[4], dev[4], sum, max;
  int head[9], diff, mindiff=INT_MAX, off_412=0;
  static const signed char dir[12][2] =
    { {-1,-1}, {-1,1}, {1,-1}, {1,1}, {-2,0}, {0,-2}, {0,2}, {2,0},
      {-2,-2}, {-2,2}, {2,-2}, {2,2} };
  float poly[8], num, cfrac, frac, mult[2], *yval[2];
  ushort *xval[2];
  int qmult_applied = 0, qlin_applied = 0;

  if (half_size || !meta_length) return;
  if (verbose) fprintf (stderr,_("Phase One correction...\n"));
  fseek (ifp, meta_offset, SEEK_SET);
  order = get2();
  fseek (ifp, 6, SEEK_CUR);
  fseek (ifp, meta_offset+get4(), SEEK_SET);
  entries = get4();  get4();
  while (entries--) {
    tag  = get4();
    len  = get4();
    data = get4();
    save = ftell(ifp);
    fseek (ifp, meta_offset+data, SEEK_SET);
    if (tag == 0x419) {				/* Polynomial curve */
      for (get4(), i=0; i < 8; i++)
	poly[i] = getreal(11);
      poly[3] += (ph1.tag_210 - poly[7]) * poly[6] + 1;
      for (i=0; i < 0x10000; i++) {
	num = (poly[5]*i + poly[3])*i + poly[1];
	curve[i] = LIM(num,0,65535);
      } goto apply;				/* apply to right half */
    } else if (tag == 0x41a) {			/* Polynomial curve */
      for (i=0; i < 4; i++)
	poly[i] = getreal(11);
      for (i=0; i < 0x10000; i++) {
	for (num=0, j=4; j--; )
	  num = num * i + poly[j];
	curve[i] = LIM(num+i,0,65535);
      } apply:					/* apply to whole image */
      for (row=0; row < raw_height; row++)
	for (col = (tag & 1)*ph1.split_col; col < raw_width; col++)
	  RAW(row,col) = curve[RAW(row,col)];
    } else if (tag == 0x400) {			/* Sensor defects */
      while ((len -= 8) >= 0) {
	col  = get2();
	row  = get2();
	type = get2(); get2();
	if (col >= raw_width) continue;
	if (type == 131 || type == 137)		/* Bad column */
	  for (row=0; row < raw_height; row++)
	    if (FC(row-top_margin,col-left_margin) == 1) {
	      for (sum=i=0; i < 4; i++)
		sum += val[i] = raw (row+dir[i][0], col+dir[i][1]);
	      for (max=i=0; i < 4; i++) {
		dev[i] = abs((val[i] << 2) - sum);
		if (dev[max] < dev[i]) max = i;
	      }
	      RAW(row,col) = (sum - val[max])/3.0 + 0.5;
	    } else {
	      for (sum=0, i=8; i < 12; i++)
		sum += raw (row+dir[i][0], col+dir[i][1]);
	      RAW(row,col) = 0.5 + sum * 0.0732233 +
		(raw(row,col-2) + raw(row,col+2)) * 0.3535534;
	    }
	else if (type == 129) {			/* Bad pixel */
	  if (row >= raw_height) continue;
	  j = (FC(row-top_margin,col-left_margin) != 1) * 4;
	  for (sum=0, i=j; i < j+8; i++)
	    sum += raw (row+dir[i][0], col+dir[i][1]);
	  RAW(row,col) = (sum + 4) >> 3;
	}
      }
    } else if (tag == 0x401) {			/* All-color flat fields */
      phase_one_flat_field (1, 2);
    } else if (tag == 0x416 || tag == 0x410) {
      phase_one_flat_field (0, 2);
    } else if (tag == 0x40b) {			/* Red+blue flat field */
      phase_one_flat_field (0, 4);
    } else if (tag == 0x412) {
      fseek (ifp, 36, SEEK_CUR);
      diff = abs (get2() - ph1.tag_21a);
      if (mindiff > diff) {
	mindiff = diff;
	off_412 = ftell(ifp) - 38;
      }
    } else if (tag == 0x41f && !qlin_applied) { /* Quadrant linearization */
      ushort lc[2][2][16], ref[16];
      int qr, qc;
      for (qr = 0; qr < 2; qr++)
	for (qc = 0; qc < 2; qc++)
	  for (i = 0; i < 16; i++)
	    lc[qr][qc][i] = get4();
      for (i = 0; i < 16; i++) {
	int v = 0;
	for (qr = 0; qr < 2; qr++)
	  for (qc = 0; qc < 2; qc++)
	    v += lc[qr][qc][i];
	ref[i] = (v + 2) >> 2;
      }
      for (qr = 0; qr < 2; qr++) {
	for (qc = 0; qc < 2; qc++) {
	  int cx[19], cf[19];
	  for (i = 0; i < 16; i++) {
	    cx[1+i] = lc[qr][qc][i];
	    cf[1+i] = ref[i];
	  }
	  cx[0] = cf[0] = 0;
	  cx[17] = cf[17] = ((unsigned) ref[15] * 65535) / lc[qr][qc][15];
	  cx[18] = cf[18] = 65535;
	  cubic_spline(cx, cf, 19);
	  for (row = (qr ? ph1.split_row : 0);
	       row < (qr ? raw_height : ph1.split_row); row++)
	    for (col = (qc ? ph1.split_col : 0);
		 col < (qc ? raw_width : ph1.split_col); col++)
	      RAW(row,col) = curve[RAW(row,col)];
	}
      }
      qlin_applied = 1;
    } else if (tag == 0x41e && !qmult_applied) { /* Quadrant multipliers */
      float qmult[2][2] = { { 1, 1 }, { 1, 1 } };
      get4(); get4(); get4(); get4();
      qmult[0][0] = 1.0 + getreal(11);
      get4(); get4(); get4(); get4(); get4();
      qmult[0][1] = 1.0 + getreal(11);
      get4(); get4(); get4();
      qmult[1][0] = 1.0 + getreal(11);
      get4(); get4(); get4();
      qmult[1][1] = 1.0 + getreal(11);
      for (row=0; row < raw_height; row++)
	for (col=0; col < raw_width; col++) {
	  i = qmult[row >= ph1.split_row][col >= ph1.split_col] * RAW(row,col);
	  RAW(row,col) = LIM(i,0,65535);
	}
      qmult_applied = 1;
    } else if (tag == 0x431 && !qmult_applied) { /* Quadrant combined */
      ushort lc[2][2][7], ref[7];
      int qr, qc;
      for (i = 0; i < 7; i++)
	ref[i] = get4();
      for (qr = 0; qr < 2; qr++)
	for (qc = 0; qc < 2; qc++)
	  for (i = 0; i < 7; i++)
	    lc[qr][qc][i] = get4();
      for (qr = 0; qr < 2; qr++) {
	for (qc = 0; qc < 2; qc++) {
	  int cx[9], cf[9];
	  for (i = 0; i < 7; i++) {
	    cx[1+i] = ref[i];
	    cf[1+i] = ((unsigned) ref[i] * lc[qr][qc][i]) / 10000;
	  }
	  cx[0] = cf[0] = 0;
	  cx[8] = cf[8] = 65535;
	  cubic_spline(cx, cf, 9);
	  for (row = (qr ? ph1.split_row : 0);
	       row < (qr ? raw_height : ph1.split_row); row++)
	    for (col = (qc ? ph1.split_col : 0);
		 col < (qc ? raw_width : ph1.split_col); col++)
	      RAW(row,col) = curve[RAW(row,col)];
        }
      }
      qmult_applied = 1;
      qlin_applied = 1;
    }
    fseek (ifp, save, SEEK_SET);
  }
  if (off_412) {
    fseek (ifp, off_412, SEEK_SET);
    for (i=0; i < 9; i++) head[i] = get4() & 0x7fff;
    yval[0] = (float *) calloc (head[1]*head[3] + head[2]*head[4], 6);
    merror (yval[0], "phase_one_correct()");
    yval[1] = (float  *) (yval[0] + head[1]*head[3]);
    xval[0] = (ushort *) (yval[1] + head[2]*head[4]);
    xval[1] = (ushort *) (xval[0] + head[1]*head[3]);
    get2();
    for (i=0; i < 2; i++)
      for (j=0; j < head[i+1]*head[i+3]; j++)
	yval[i][j] = getreal(11);
    for (i=0; i < 2; i++)
      for (j=0; j < head[i+1]*head[i+3]; j++)
	xval[i][j] = get2();
    for (row=0; row < raw_height; row++)
      for (col=0; col < raw_width; col++) {
	cfrac = (float) col * head[3] / raw_width;
	cfrac -= cip = cfrac;
	num = RAW(row,col) * 0.5;
	for (i=cip; i < cip+2; i++) {
	  for (k=j=0; j < head[1]; j++)
	    if (num < xval[0][k = head[1]*i+j]) break;
	  frac = (j == 0 || j == head[1]) ? 0 :
		(xval[0][k] - num) / (xval[0][k] - xval[0][k-1]);
	  mult[i-cip] = yval[0][k-1] * frac + yval[0][k] * (1-frac);
	}
	i = ((mult[0] * (1-cfrac) + mult[1] * cfrac) * row + num) * 2;
	RAW(row,col) = LIM(i,0,65535);
      }
    free (yval[0]);
  }
}

void CLASS phase_one_load_raw()
{
  int a, b, i;
  ushort akey, bkey, mask;

  fseek (ifp, ph1.key_off, SEEK_SET);
  akey = get2();
  bkey = get2();
  mask = ph1.format == 1 ? 0x5555:0x1354;
  fseek (ifp, data_offset, SEEK_SET);
  read_shorts (raw_image, raw_width*raw_height);
  if (ph1.format)
    for (i=0; i < raw_width*raw_height; i+=2) {
      a = raw_image[i+0] ^ akey;
      b = raw_image[i+1] ^ bkey;
      raw_image[i+0] = (a & mask) | (b & ~mask);
      raw_image[i+1] = (b & mask) | (a & ~mask);
    }
}

unsigned CLASS ph1_bithuff (int nbits, ushort *huff)
{
  static UINT64 bitbuf=0;
  static int vbits=0;
  unsigned c;

  if (nbits == -1)
    return bitbuf = vbits = 0;
  if (nbits == 0) return 0;
  if (vbits < nbits) {
    bitbuf = bitbuf << 32 | get4();
    vbits += 32;
  }
  c = bitbuf << (64-vbits) >> (64-nbits);
  if (huff) {
    vbits -= huff[c] >> 8;
    return (uchar) huff[c];
  }
  vbits -= nbits;
  return c;
}
#define ph1_bits(n) ph1_bithuff(n,0)
#define ph1_huff(h) ph1_bithuff(*h,h+1)

void CLASS phase_one_load_raw_c()
{
  static const int length[] = { 8,7,6,9,11,10,5,12,14,13 };
  int *offset, len[2], pred[2], row, col, i, j;
  ushort *pixel;
  short (*cblack)[2], (*rblack)[2];

  pixel = (ushort *) calloc (raw_width*3 + raw_height*4, 2);
  merror (pixel, "phase_one_load_raw_c()");
  offset = (int *) (pixel + raw_width);
  fseek (ifp, strip_offset, SEEK_SET);
  for (row=0; row < raw_height; row++)
    offset[row] = get4();
  cblack = (short (*)[2]) (offset + raw_height);
  fseek (ifp, ph1.black_col, SEEK_SET);
  if (ph1.black_col)
    read_shorts ((ushort *) cblack[0], raw_height*2);
  rblack = cblack + raw_height;
  fseek (ifp, ph1.black_row, SEEK_SET);
  if (ph1.black_row)
    read_shorts ((ushort *) rblack[0], raw_width*2);
  for (i=0; i < 256; i++)
    curve[i] = i*i / 3.969 + 0.5;
  for (row=0; row < raw_height; row++) {
    fseek (ifp, data_offset + offset[row], SEEK_SET);
    ph1_bits(-1);
    pred[0] = pred[1] = 0;
    for (col=0; col < raw_width; col++) {
      if (col >= (raw_width & -8))
	len[0] = len[1] = 14;
      else if ((col & 7) == 0)
	for (i=0; i < 2; i++) {
	  for (j=0; j < 5 && !ph1_bits(1); j++);
	  if (j--) len[i] = length[j*2 + ph1_bits(1)];
	}
      if ((i = len[col & 1]) == 14)
	pixel[col] = pred[col & 1] = ph1_bits(16);
      else
	pixel[col] = pred[col & 1] += ph1_bits(i) + 1 - (1 << (i - 1));
      if (pred[col & 1] >> 16) derror();
      if (ph1.format == 5 && pixel[col] < 256)
	pixel[col] = curve[pixel[col]];
    }
    for (col=0; col < raw_width; col++) {
      i = (pixel[col] << 2*(ph1.format != 8)) - ph1.black
	+ cblack[row][col >= ph1.split_col]
	+ rblack[col][row >= ph1.split_row];
      if (i > 0) RAW(row,col) = i;
    }
  }
  free (pixel);
  maximum = 0xfffc - ph1.black;
}

void CLASS load_raw8()
{
  uchar  *data,  *dp;
  int rev, dwide, row, col, c;
  double sum[]={0,0};
  rev = 3 * (order == 0x4949);
  if (raw_stride == 0)
    dwide = raw_width;
  else
    dwide = raw_stride;
  data = (uchar *) malloc (dwide*2);
  merror (data, "load_raw8()");
  for (row=0; row < raw_height; row++) {
    if (fread (data+dwide, 1, dwide, ifp) < dwide) derror();
    FORC(dwide) data[c] = data[dwide+(c ^ rev)];
    for (dp=data, col=0; col < raw_width; dp++, col++)
      RAW(row,col+c) = dp[c];
  }
  free (data);
  maximum = 0xff;
  if (!strcmp(make,"RaspberryPi")) return;

  row = raw_height/2;
  FORC(width-1) {
    sum[ c & 1] += SQR(RAW(row,c)-RAW(row+1,c+1));
    sum[~c & 1] += SQR(RAW(row+1,c)-RAW(row,c+1));
  }
  if (sum[1] > sum[0]) filters = 0x4b4b4b4b;
}

void CLASS nokia_load_raw()
{
  uchar  *data,  *dp;
  int rev, dwide, row, col, c;
  double sum[]={0,0};
  rev = 3 * (order == 0x4949);
  if (raw_stride == 0)
    dwide = (raw_width * 5 + 1) / 4;
  else
    dwide = raw_stride;
  data = (uchar *) malloc (dwide*2);
  merror (data, "nokia_load_raw()");
  for (row=0; row < raw_height; row++) {
    if (fread (data+dwide, 1, dwide, ifp) < dwide) derror();
    FORC(dwide) data[c] = data[dwide+(c ^ rev)];
    for (dp=data, col=0; col < raw_width; dp+=5, col+=4)
      FORC4 RAW(row,col+c) = (dp[c] << 2) | (dp[4] >> (c << 1) & 3);
  }
  free (data);
  maximum = 0x3ff;
  if (!strcmp(make,"RaspberryPi")) return;

  row = raw_height/2;
  FORC(width-1) {
    sum[ c & 1] += SQR(RAW(row,c)-RAW(row+1,c+1));
    sum[~c & 1] += SQR(RAW(row+1,c)-RAW(row,c+1));
  }
  if (sum[1] > sum[0]) filters = 0x4b4b4b4b;
}

void CLASS load_raw12()
{
  uchar  *data,  *dp;
  int rev, dwide, row, col, c;
  double sum[]={0,0};
  rev = 3 * (order == 0x4949);
  if (raw_stride == 0)
    dwide = (raw_width * 3 + 1) / 2;
  else
    dwide = raw_stride;
  data = (uchar *) malloc (dwide*2);
  merror (data, "load_raw12()");
  for (row=0; row < raw_height; row++) {
    if (fread (data+dwide, 1, dwide, ifp) < dwide) derror();
    FORC(dwide) data[c] = data[dwide+(c ^ rev)];
    for (dp=data, col=0; col < raw_width; dp+=3, col+=2)
      FORC2 RAW(row,col+c) = (dp[c] << 4) | (dp[2] >> (c << 2) & 0xF);
  }
  free (data);
  maximum = 0xfff;
  if (!strcmp(make,"RaspberryPi")) return;

  row = raw_height/2;
  FORC(width-1) {
    sum[ c & 1] += SQR(RAW(row,c)-RAW(row+1,c+1));
    sum[~c & 1] += SQR(RAW(row+1,c)-RAW(row,c+1));
  }
  if (sum[1] > sum[0]) filters = 0x4b4b4b4b;
}

void CLASS load_raw14()
{
  uchar  *data,  *dp;
  int rev, dwide, row, col, c;
  double sum[]={0,0};
  rev = 3 * (order == 0x4949);
  if (raw_stride == 0)
    dwide = ((raw_width*7)+3)>>2;
  else
    dwide = raw_stride;
  data = (uchar *) malloc (dwide*2);
  merror (data, "load_raw14()");
  for (row=0; row < raw_height; row++) {
    if (fread (data+dwide, 1, dwide, ifp) < dwide) derror();
    FORC(dwide) data[c] = data[dwide+(c ^ rev)];
    for (dp=data, col=0; col < raw_width; dp+=7, col+=4) {
      RAW(row,col+0) = (dp[0] << 6) | (dp[4] >> 2);
      RAW(row,col+1) = (dp[1] << 6) | ((dp[4] & 0x3) << 4) | ((dp[5] & 0xf0) >> 4);
      RAW(row,col+2) = (dp[2] << 6) | ((dp[5] & 0xf) << 2) | ((dp[6] & 0xc0) >> 6);
      RAW(row,col+3) = (dp[3] << 6) | ((dp[6] & 0x3f) << 2);
    }
  }
  free (data);
  maximum = 0x3fff;
  if (!strcmp(make,"RaspberryPi")) return;

  row = raw_height/2;
  FORC(width-1) {
    sum[ c & 1] += SQR(RAW(row,c)-RAW(row+1,c+1));
    sum[~c & 1] += SQR(RAW(row+1,c)-RAW(row,c+1));
  }
  if (sum[1] > sum[0]) filters = 0x4b4b4b4b;
}

void CLASS load_raw16()
{
  uchar  *data,  *dp;
  int rev, dwide, row, col, c;
  double sum[]={0,0};
  rev = 3 * (order == 0x4949);
  if (raw_stride == 0)
    dwide = (raw_width * 2);
  else
    dwide = raw_stride;
  data = (uchar *) malloc (dwide*2);
  merror (data, "load_raw16()");
  for (row=0; row < raw_height; row++) {
    if (fread (data+dwide, 1, dwide, ifp) < dwide) derror();
    FORC(dwide) data[c] = data[dwide+(c ^ rev)];
    for (dp=data, col=0; col < raw_width; dp+=2, col++)
      RAW(row,col+c) = (dp[1] << 8) | dp[0];
  }
  free (data);
  maximum = 0xffff;
  if (!strcmp(make,"RaspberryPi")) return;

  row = raw_height/2;
  FORC(width-1) {
    sum[ c & 1] += SQR(RAW(row,c)-RAW(row+1,c+1));
    sum[~c & 1] += SQR(RAW(row+1,c)-RAW(row,c+1));
  }
  if (sum[1] > sum[0]) filters = 0x4b4b4b4b;
}

void CLASS gamma_curve (double pwr, double ts, int mode, int imax);

void CLASS crop_masked_pixels()
{
  int row, col;
  unsigned r, c, m, mblack[8], zero, val;

  if (load_raw == &CLASS phase_one_load_raw ||
      load_raw == &CLASS phase_one_load_raw_c)
    phase_one_correct();


    for (row=0; row < height; row++)
      for (col=0; col < width; col++)
	BAYER2(row,col) = RAW(row+top_margin,col+left_margin);

  if (mask[0][3] > 0) goto mask_set;
  if (load_raw == &CLASS nokia_load_raw) {
    mask[0][2] = top_margin;
    mask[0][3] = width;
  }
mask_set:
  memset (mblack, 0, sizeof mblack);
  for (zero=m=0; m < 8; m++)
    for (row=MAX(mask[m][0],0); row < MIN(mask[m][2],raw_height); row++)
      for (col=MAX(mask[m][1],0); col < MIN(mask[m][3],raw_width); col++) {
	c = FC(row-top_margin,col-left_margin);
	mblack[c] += val = RAW(row,col);
	mblack[4+c]++;
	zero += !val;
      }
  if (zero < mblack[4] && mblack[5] && mblack[6] && mblack[7]) {
    FORC4 cblack[c] = mblack[c] / mblack[4+c];
    cblack[4] = cblack[5] = cblack[6] = 0;
  }
}

void CLASS remove_zeroes()
{
  unsigned row, col, tot, n, r, c;

  for (row=0; row < height; row++)
    for (col=0; col < width; col++)
      if (BAYER(row,col) == 0) {
	tot = n = 0;
	for (r = row-2; r <= row+2; r++)
	  for (c = col-2; c <= col+2; c++)
	    if (r < height && c < width &&
		FC(r,c) == FC(row,col) && BAYER(r,c))
	      tot += (n++,BAYER(r,c));
	if (n) BAYER(row,col) = tot/n;
      }
}

/*
   Seach from the current directory up to the root looking for
   a ".badpixels" file, and fix those pixels now.
 */
void CLASS bad_pixels (const char *cfname)
{
  FILE *fp=0;
  char *fname, *cp, line[128];
  int len, time, row, col, r, c, rad, tot, n, fixed=0;

  if (!filters) return;
  if (cfname)
    fp = fopen (cfname, "r");
  else {
    for (len=32 ; ; len *= 2) {
      fname = (char *) malloc (len);
      if (!fname) return;
      if (getcwd (fname, len-16)) break;
      free (fname);
      if (errno != ERANGE) return;
    }
#if defined(WIN32) || defined(DJGPP)
    if (fname[1] == ':')
      memmove (fname, fname+2, len-2);
    for (cp=fname; *cp; cp++)
      if (*cp == '\\') *cp = '/';
#endif
    cp = fname + strlen(fname);
    if (cp[-1] == '/') cp--;
    while (*fname == '/') {
      strcpy (cp, "/.badpixels");
      if ((fp = fopen (fname, "r"))) break;
      if (cp == fname) break;
      while (*--cp != '/');
    }
    free (fname);
  }
  if (!fp) return;
  while (fgets (line, 128, fp)) {
    cp = strchr (line, '#');
    if (cp) *cp = 0;
    if (sscanf (line, "%d %d %d", &col, &row, &time) != 3) continue;
    if ((unsigned) col >= width || (unsigned) row >= height) continue;
    if (time > timestamp) continue;
    for (tot=n=0, rad=1; rad < 3 && n==0; rad++)
      for (r = row-rad; r <= row+rad; r++)
	for (c = col-rad; c <= col+rad; c++)
	  if ((unsigned) r < height && (unsigned) c < width &&
		(r != row || c != col) && fcol(r,c) == fcol(row,col)) {
	    tot += BAYER2(r,c);
	    n++;
	  }
    BAYER2(row,col) = tot/n;
    if (verbose) {
      if (!fixed++)
	fprintf (stderr,_("Fixed dead pixels at:"));
      fprintf (stderr, " %d,%d", col, row);
    }
  }
  if (fixed) fputc ('\n', stderr);
  fclose (fp);
}

void CLASS gamma_curve (double pwr, double ts, int mode, int imax)
{
  int i;
  double g[6], bnd[2]={0,0}, r;

  g[0] = pwr;
  g[1] = ts;
  g[2] = g[3] = g[4] = 0;
  bnd[g[1] >= 1] = 1;
  if (g[1] && (g[1]-1)*(g[0]-1) <= 0) {
    for (i=0; i < 48; i++) {
      g[2] = (bnd[0] + bnd[1])/2;
      if (g[0]) bnd[(pow(g[2]/g[1],-g[0]) - 1)/g[0] - 1/g[2] > -1] = g[2];
      else	bnd[g[2]/exp(1-1/g[2]) < g[1]] = g[2];
    }
    g[3] = g[2] / g[1];
    if (g[0]) g[4] = g[2] * (1/g[0] - 1);
  }
  if (g[0]) g[5] = 1 / (g[1]*SQR(g[3])/2 - g[4]*(1 - g[3]) +
		(1 - pow(g[3],1+g[0]))*(1 + g[4])/(1 + g[0])) - 1;
  else      g[5] = 1 / (g[1]*SQR(g[3])/2 + 1
		- g[2] - g[3] -	g[2]*g[3]*(log(g[3]) - 1)) - 1;
  if (!mode--) {
    memcpy (gamm, g, sizeof gamm);
    return;
  }
  for (i=0; i < 0x10000; i++) {
    curve[i] = 0xffff;
    if ((r = (double) i / imax) < 1)
      curve[i] = 0x10000 * ( mode
	? (r < g[3] ? r*g[1] : (g[0] ? pow( r,g[0])*(1+g[4])-g[4]    : log(r)*g[2]+1))
	: (r < g[2] ? r/g[1] : (g[0] ? pow((r+g[4])/(1+g[4]),1/g[0]) : exp((r-1)/g[2]))));
  }
}

void CLASS pseudoinverse (double (*in)[3], double (*out)[3], int size)
{
  double work[3][6], num;
  int i, j, k;

  for (i=0; i < 3; i++) {
    for (j=0; j < 6; j++)
      work[i][j] = j == i+3;
    for (j=0; j < 3; j++)
      for (k=0; k < size; k++)
	work[i][j] += in[k][i] * in[k][j];
  }
  for (i=0; i < 3; i++) {
    num = work[i][i];
    for (j=0; j < 6; j++)
      work[i][j] /= num;
    for (k=0; k < 3; k++) {
      if (k==i) continue;
      num = work[k][i];
      for (j=0; j < 6; j++)
	work[k][j] -= work[i][j] * num;
    }
  }
  for (i=0; i < size; i++)
    for (j=0; j < 3; j++)
      for (out[i][j]=k=0; k < 3; k++)
	out[i][j] += work[j][k+3] * in[i][k];
}

void CLASS cam_xyz_coeff (float rgb_cam[3][4], double cam_xyz[4][3])
{
  double cam_rgb[4][3], inverse[4][3], num;
  int i, j, k;

  for (i=0; i < colors; i++)		/* Multiply out XYZ colorspace */
    for (j=0; j < 3; j++)
      for (cam_rgb[i][j] = k=0; k < 3; k++)
	cam_rgb[i][j] += cam_xyz[i][k] * xyz_rgb[k][j];

  for (i=0; i < colors; i++) {		/* Normalize cam_rgb so that */
    for (num=j=0; j < 3; j++)		/* cam_rgb * (1,1,1) is (1,1,1,1) */
      num += cam_rgb[i][j];
    for (j=0; j < 3; j++)
      cam_rgb[i][j] /= num;
    pre_mul[i] = 1 / num;
  }
  pseudoinverse (cam_rgb, inverse, colors);
  for (i=0; i < 3; i++)
    for (j=0; j < colors; j++)
      rgb_cam[i][j] = inverse[j][i];
}

void CLASS hat_transform (float *temp, float *base, int st, int size, int sc)
{
  int i;
  for (i=0; i < sc; i++)
    temp[i] = 2*base[st*i] + base[st*(sc-i)] + base[st*(i+sc)];
  for (; i+sc < size; i++)
    temp[i] = 2*base[st*i] + base[st*(i-sc)] + base[st*(i+sc)];
  for (; i < size; i++)
    temp[i] = 2*base[st*i] + base[st*(i-sc)] + base[st*(2*size-2-(i+sc))];
}

void CLASS wavelet_denoise()
{
  float *fimg=0, *temp, thold, mul[2], avg, diff;
  int scale=1, size, lev, hpass, lpass, row, col, nc, c, i, wlast, blk[2];
  ushort *window[4];
  static const float noise[] =
  { 0.8002,0.2735,0.1202,0.0585,0.0291,0.0152,0.0080,0.0044 };

  if (verbose) fprintf (stderr,_("Wavelet denoising...\n"));

  while (maximum << scale < 0x10000) scale++;
  maximum <<= --scale;
  black <<= scale;
  FORC4 cblack[c] <<= scale;
  if ((size = iheight*iwidth) < 0x15550000)
    fimg = (float *) malloc ((size*3 + iheight + iwidth) * sizeof *fimg);
  merror (fimg, "wavelet_denoise()");
  temp = fimg + size*3;
  if ((nc = colors) == 3 && filters) nc++;
  FORC(nc) {			/* denoise R,G1,B,G3 individually */
    for (i=0; i < size; i++)
      fimg[i] = 256 * sqrt(image[i][c] << scale);
    for (hpass=lev=0; lev < 5; lev++) {
      lpass = size*((lev & 1)+1);
      for (row=0; row < iheight; row++) {
	hat_transform (temp, fimg+hpass+row*iwidth, 1, iwidth, 1 << lev);
	for (col=0; col < iwidth; col++)
	  fimg[lpass + row*iwidth + col] = temp[col] * 0.25;
      }
      for (col=0; col < iwidth; col++) {
	hat_transform (temp, fimg+lpass+col, iwidth, iheight, 1 << lev);
	for (row=0; row < iheight; row++)
	  fimg[lpass + row*iwidth + col] = temp[row] * 0.25;
      }
      thold = threshold * noise[lev];
      for (i=0; i < size; i++) {
	fimg[hpass+i] -= fimg[lpass+i];
	if	(fimg[hpass+i] < -thold) fimg[hpass+i] += thold;
	else if (fimg[hpass+i] >  thold) fimg[hpass+i] -= thold;
	else	 fimg[hpass+i] = 0;
	if (hpass) fimg[i] += fimg[hpass+i];
      }
      hpass = lpass;
    }
    for (i=0; i < size; i++)
      image[i][c] = CLIP(SQR(fimg[i]+fimg[lpass+i])/0x10000);
  }
  if (filters && colors == 3) {  /* pull G1 and G3 closer together */
    for (row=0; row < 2; row++) {
      mul[row] = 0.125 * pre_mul[FC(row+1,0) | 1] / pre_mul[FC(row,0) | 1];
      blk[row] = cblack[FC(row,0) | 1];
    }
    for (i=0; i < 4; i++)
      window[i] = (ushort *) fimg + width*i;
    for (wlast=-1, row=1; row < height-1; row++) {
      while (wlast < row+1) {
	for (wlast++, i=0; i < 4; i++)
	  window[(i+3) & 3] = window[i];
	for (col = FC(wlast,1) & 1; col < width; col+=2)
	  window[2][col] = BAYER(wlast,col);
      }
      thold = threshold/512;
      for (col = (FC(row,0) & 1)+1; col < width-1; col+=2) {
	avg = ( window[0][col-1] + window[0][col+1] +
		window[2][col-1] + window[2][col+1] - blk[~row & 1]*4 )
	      * mul[row & 1] + (window[1][col] + blk[row & 1]) * 0.5;
	avg = avg < 0 ? 0 : sqrt(avg);
	diff = sqrt(BAYER(row,col)) - avg;
	if      (diff < -thold) diff += thold;
	else if (diff >  thold) diff -= thold;
	else diff = 0;
	BAYER(row,col) = CLIP(SQR(avg+diff) + 0.5);
      }
    }
  }
  free (fimg);
}

void CLASS scale_colors()
{
  unsigned bottom, right, size, row, col, ur, uc, i, x, y, c, sum[8];
  int val, dark, sat;
  double dsum[8], dmin, dmax;
  float scale_mul[4], fr, fc;
  ushort *img=0, *pix;

  if (user_mul[0])
    memcpy (pre_mul, user_mul, sizeof pre_mul);
  if (use_auto_wb || (use_camera_wb && cam_mul[0] == -1)) {
    memset (dsum, 0, sizeof dsum);
    bottom = MIN (greybox[1]+greybox[3], height);
    right  = MIN (greybox[0]+greybox[2], width);
    for (row=greybox[1]; row < bottom; row += 8)
      for (col=greybox[0]; col < right; col += 8) {
	memset (sum, 0, sizeof sum);
	for (y=row; y < row+8 && y < bottom; y++)
	  for (x=col; x < col+8 && x < right; x++)
	    FORC4 {
	      if (filters) {
		c = fcol(y,x);
		val = BAYER2(y,x);
	      } else
		val = image[y*width+x][c];
	      if (val > maximum-25) goto skip_block;
	      if ((val -= cblack[c]) < 0) val = 0;
	      sum[c] += val;
	      sum[c+4]++;
	      if (filters) break;
	    }
	FORC(8) dsum[c] += sum[c];
skip_block: ;
      }
    FORC4 if (dsum[c]) pre_mul[c] = dsum[c+4] / dsum[c];
  }
  if (use_camera_wb && cam_mul[0] != -1) {
    memset (sum, 0, sizeof sum);
    for (row=0; row < 8; row++)
      for (col=0; col < 8; col++) {
	c = FC(row,col);
	if ((val = white[row][col] - cblack[c]) > 0)
	  sum[c] += val;
	sum[c+4]++;
      }
    if (sum[0] && sum[1] && sum[2] && sum[3])
      FORC4 pre_mul[c] = (float) sum[c+4] / sum[c];
    else if (cam_mul[0] && cam_mul[2])
      memcpy (pre_mul, cam_mul, sizeof pre_mul);
    else
      fprintf (stderr,_("%s: Cannot use camera white balance.\n"), ifname);
  }
  if (pre_mul[1] == 0) pre_mul[1] = 1;
  if (pre_mul[3] == 0) pre_mul[3] = colors < 4 ? pre_mul[1] : 1;
  dark = black;
  sat = maximum;
  if (threshold) wavelet_denoise();
  maximum -= black;
  for (dmin=DBL_MAX, dmax=c=0; c < 4; c++) {
    if (dmin > pre_mul[c])
	dmin = pre_mul[c];
    if (dmax < pre_mul[c])
	dmax = pre_mul[c];
  }
  if (!highlight) dmax = dmin;
  FORC4 scale_mul[c] = (pre_mul[c] /= dmax) * 65535.0 / maximum;
  if (verbose) {
    fprintf (stderr,
      _("Scaling with darkness %d, saturation %d, and\nmultipliers"), dark, sat);
    FORC4 fprintf (stderr, " %f", pre_mul[c]);
    fputc ('\n', stderr);
  }
  if (filters > 1000 && (cblack[4]+1)/2 == 1 && (cblack[5]+1)/2 == 1) {
    FORC4 cblack[FC(c/2,c%2)] +=
	cblack[6 + c/2 % cblack[4] * cblack[5] + c%2 % cblack[5]];
    cblack[4] = cblack[5] = 0;
  }
  size = iheight*iwidth;
  for (i=0; i < size*4; i++) {
    if (!(val = ((ushort *)image)[i])) continue;
    if (cblack[4] && cblack[5])
      val -= cblack[6 + i/4 / iwidth % cblack[4] * cblack[5] +
			i/4 % iwidth % cblack[5]];
    val -= cblack[i & 3];
    val *= scale_mul[i & 3];
    ((ushort *)image)[i] = CLIP(val);
  }
  if ((aber[0] != 1 || aber[2] != 1) && colors == 3) {
    if (verbose)
      fprintf (stderr,_("Correcting chromatic aberration...\n"));
    for (c=0; c < 4; c+=2) {
      if (aber[c] == 1) continue;
      img = (ushort *) malloc (size * sizeof *img);
      merror (img, "scale_colors()");
      for (i=0; i < size; i++)
	img[i] = image[i][c];
      for (row=0; row < iheight; row++) {
	ur = fr = (row - iheight*0.5) * aber[c] + iheight*0.5;
	if (ur > iheight-2) continue;
	fr -= ur;
	for (col=0; col < iwidth; col++) {
	  uc = fc = (col - iwidth*0.5) * aber[c] + iwidth*0.5;
	  if (uc > iwidth-2) continue;
	  fc -= uc;
	  pix = img + ur*iwidth + uc;
	  image[row*iwidth+col][c] =
	    (pix[     0]*(1-fc) + pix[       1]*fc) * (1-fr) +
	    (pix[iwidth]*(1-fc) + pix[iwidth+1]*fc) * fr;
	}
      }
      free(img);
    }
  }
}

void CLASS pre_interpolate()
{
  ushort (*img)[4];
  int row, col, c;

  if (shrink) {
    if (half_size) {
      height = iheight;
      width  = iwidth;
      if (filters == 9) {
	for (row=0; row < 3; row++)
	  for (col=1; col < 4; col++)
	    if (!(image[row*width+col][0] | image[row*width+col][2]))
	      goto break2;  break2:
	for ( ; row < height; row+=3)
	  for (col=(col-1)%3+1; col < width-1; col+=3) {
	    img = image + row*width+col;
	    for (c=0; c < 3; c+=2)
	      img[0][c] = (img[-1][c] + img[1][c]) >> 1;
	  }
      }
    } else {
      img = (ushort (*)[4]) calloc (height, width*sizeof *img);
      merror (img, "pre_interpolate()");
      for (row=0; row < height; row++)
	for (col=0; col < width; col++) {
	  c = fcol(row,col);
	  img[row*width+col][c] = image[(row >> 1)*iwidth+(col >> 1)][c];
	}
      free (image);
      image = img;
      shrink = 0;
    }
  }
  if (filters > 1000 && colors == 3) {
    mix_green = four_color_rgb ^ half_size;
    if (four_color_rgb | half_size) colors++;
    else {
      for (row = FC(1,0) >> 1; row < height; row+=2)
	for (col = FC(row,1) & 1; col < width; col+=2)
	  image[row*width+col][1] = image[row*width+col][3];
      filters &= ~((filters & 0x55555555) << 1);
    }
  }
  if (half_size) filters = 0;
}

void CLASS border_interpolate (int border)
{
  unsigned row, col, y, x, f, c, sum[8];

  for (row=0; row < height; row++)
    for (col=0; col < width; col++) {
      if (col==border && row >= border && row < height-border)
	col = width-border;
      memset (sum, 0, sizeof sum);
      for (y=row-1; y != row+2; y++)
	for (x=col-1; x != col+2; x++)
	  if (y < height && x < width) {
	    f = fcol(y,x);
	    sum[f] += image[y*width+x][f];
	    sum[f+4]++;
	  }
      f = fcol(row,col);
      FORCC if (c != f && sum[c+4])
	image[row*width+col][c] = sum[c] / sum[c+4];
    }
}

void CLASS lin_interpolate()
{
  int code[16][16][32], size=16, *ip, sum[4];
  int f, c, i, x, y, row, col, shift, color;
  ushort *pix;

  if (verbose) fprintf (stderr,_("Bilinear interpolation...\n"));
  if (filters == 9) size = 6;
  border_interpolate(1);
  for (row=0; row < size; row++)
    for (col=0; col < size; col++) {
      ip = code[row][col]+1;
      f = fcol(row,col);
      memset (sum, 0, sizeof sum);
      for (y=-1; y <= 1; y++)
	for (x=-1; x <= 1; x++) {
	  shift = (y==0) + (x==0);
	  color = fcol(row+y,col+x);
	  if (color == f) continue;
	  *ip++ = (width*y + x)*4 + color;
	  *ip++ = shift;
	  *ip++ = color;
	  sum[color] += 1 << shift;
	}
      code[row][col][0] = (ip - code[row][col]) / 3;
      FORCC
	if (c != f) {
	  *ip++ = c;
	  *ip++ = 256 / sum[c];
	}
    }
  for (row=1; row < height-1; row++)
    for (col=1; col < width-1; col++) {
      pix = image[row*width+col];
      ip = code[row % size][col % size];
      memset (sum, 0, sizeof sum);
      for (i=*ip++; i--; ip+=3)
	sum[ip[2]] += pix[ip[0]] << ip[1];
      for (i=colors; --i; ip+=2)
	pix[ip[0]] = sum[ip[0]] * ip[1] >> 8;
    }
}

/*
   This algorithm is officially called:

   "Interpolation using a Threshold-based variable number of gradients"

   described in http://scien.stanford.edu/pages/labsite/1999/psych221/projects/99/tingchen/algodep/vargra.html

   I've extended the basic idea to work with non-Bayer filter arrays.
   Gradients are numbered clockwise from NW=0 to W=7.
 */
void CLASS vng_interpolate()
{
  static const signed char *cp, terms[] = {
    -2,-2,+0,-1,0,0x01, -2,-2,+0,+0,1,0x01, -2,-1,-1,+0,0,0x01,
    -2,-1,+0,-1,0,0x02, -2,-1,+0,+0,0,0x03, -2,-1,+0,+1,1,0x01,
    -2,+0,+0,-1,0,0x06, -2,+0,+0,+0,1,0x02, -2,+0,+0,+1,0,0x03,
    -2,+1,-1,+0,0,0x04, -2,+1,+0,-1,1,0x04, -2,+1,+0,+0,0,0x06,
    -2,+1,+0,+1,0,0x02, -2,+2,+0,+0,1,0x04, -2,+2,+0,+1,0,0x04,
    -1,-2,-1,+0,0,0x80, -1,-2,+0,-1,0,0x01, -1,-2,+1,-1,0,0x01,
    -1,-2,+1,+0,1,0x01, -1,-1,-1,+1,0,0x88, -1,-1,+1,-2,0,0x40,
    -1,-1,+1,-1,0,0x22, -1,-1,+1,+0,0,0x33, -1,-1,+1,+1,1,0x11,
    -1,+0,-1,+2,0,0x08, -1,+0,+0,-1,0,0x44, -1,+0,+0,+1,0,0x11,
    -1,+0,+1,-2,1,0x40, -1,+0,+1,-1,0,0x66, -1,+0,+1,+0,1,0x22,
    -1,+0,+1,+1,0,0x33, -1,+0,+1,+2,1,0x10, -1,+1,+1,-1,1,0x44,
    -1,+1,+1,+0,0,0x66, -1,+1,+1,+1,0,0x22, -1,+1,+1,+2,0,0x10,
    -1,+2,+0,+1,0,0x04, -1,+2,+1,+0,1,0x04, -1,+2,+1,+1,0,0x04,
    +0,-2,+0,+0,1,0x80, +0,-1,+0,+1,1,0x88, +0,-1,+1,-2,0,0x40,
    +0,-1,+1,+0,0,0x11, +0,-1,+2,-2,0,0x40, +0,-1,+2,-1,0,0x20,
    +0,-1,+2,+0,0,0x30, +0,-1,+2,+1,1,0x10, +0,+0,+0,+2,1,0x08,
    +0,+0,+2,-2,1,0x40, +0,+0,+2,-1,0,0x60, +0,+0,+2,+0,1,0x20,
    +0,+0,+2,+1,0,0x30, +0,+0,+2,+2,1,0x10, +0,+1,+1,+0,0,0x44,
    +0,+1,+1,+2,0,0x10, +0,+1,+2,-1,1,0x40, +0,+1,+2,+0,0,0x60,
    +0,+1,+2,+1,0,0x20, +0,+1,+2,+2,0,0x10, +1,-2,+1,+0,0,0x80,
    +1,-1,+1,+1,0,0x88, +1,+0,+1,+2,0,0x08, +1,+0,+2,-1,0,0x40,
    +1,+0,+2,+1,0,0x10
  }, chood[] = { -1,-1, -1,0, -1,+1, 0,+1, +1,+1, +1,0, +1,-1, 0,-1 };
  ushort (*brow[5])[4], *pix;
  int prow=8, pcol=2, *ip, *code[16][16], gval[8], gmin, gmax, sum[4];
  int row, col, x, y, x1, x2, y1, y2, t, weight, grads, color, diag;
  int g, diff, thold, num, c;

  lin_interpolate();
  if (verbose) fprintf (stderr,_("VNG interpolation...\n"));

  if (filters == 1) prow = pcol = 16;
  if (filters == 9) prow = pcol =  6;
  ip = (int *) calloc (prow*pcol, 1280);
  merror (ip, "vng_interpolate()");
  for (row=0; row < prow; row++)		/* Precalculate for VNG */
    for (col=0; col < pcol; col++) {
      code[row][col] = ip;
      for (cp=terms, t=0; t < 64; t++) {
	y1 = *cp++;  x1 = *cp++;
	y2 = *cp++;  x2 = *cp++;
	weight = *cp++;
	grads = *cp++;
	color = fcol(row+y1,col+x1);
	if (fcol(row+y2,col+x2) != color) continue;
	diag = (fcol(row,col+1) == color && fcol(row+1,col) == color) ? 2:1;
	if (abs(y1-y2) == diag && abs(x1-x2) == diag) continue;
	*ip++ = (y1*width + x1)*4 + color;
	*ip++ = (y2*width + x2)*4 + color;
	*ip++ = weight;
	for (g=0; g < 8; g++)
	  if (grads & 1<<g) *ip++ = g;
	*ip++ = -1;
      }
      *ip++ = INT_MAX;
      for (cp=chood, g=0; g < 8; g++) {
	y = *cp++;  x = *cp++;
	*ip++ = (y*width + x) * 4;
	color = fcol(row,col);
	if (fcol(row+y,col+x) != color && fcol(row+y*2,col+x*2) == color)
	  *ip++ = (y*width + x) * 8 + color;
	else
	  *ip++ = 0;
      }
    }
  brow[4] = (ushort (*)[4]) calloc (width*3, sizeof **brow);
  merror (brow[4], "vng_interpolate()");
  for (row=0; row < 3; row++)
    brow[row] = brow[4] + row*width;
  for (row=2; row < height-2; row++) {		/* Do VNG interpolation */
    for (col=2; col < width-2; col++) {
      pix = image[row*width+col];
      ip = code[row % prow][col % pcol];
      memset (gval, 0, sizeof gval);
      while ((g = ip[0]) != INT_MAX) {		/* Calculate gradients */
	diff = ABS(pix[g] - pix[ip[1]]) << ip[2];
	gval[ip[3]] += diff;
	ip += 5;
	if ((g = ip[-1]) == -1) continue;
	gval[g] += diff;
	while ((g = *ip++) != -1)
	  gval[g] += diff;
      }
      ip++;
      gmin = gmax = gval[0];			/* Choose a threshold */
      for (g=1; g < 8; g++) {
	if (gmin > gval[g]) gmin = gval[g];
	if (gmax < gval[g]) gmax = gval[g];
      }
      if (gmax == 0) {
	memcpy (brow[2][col], pix, sizeof *image);
	continue;
      }
      thold = gmin + (gmax >> 1);
      memset (sum, 0, sizeof sum);
      color = fcol(row,col);
      for (num=g=0; g < 8; g++,ip+=2) {		/* Average the neighbors */
	if (gval[g] <= thold) {
	  FORCC
	    if (c == color && ip[1])
	      sum[c] += (pix[c] + pix[ip[1]]) >> 1;
	    else
	      sum[c] += pix[ip[0] + c];
	  num++;
	}
      }
      FORCC {					/* Save to buffer */
	t = pix[color];
	if (c != color)
	  t += (sum[c] - sum[color]) / num;
	brow[2][col][c] = CLIP(t);
      }
    }
    if (row > 3)				/* Write buffer to image */
      memcpy (image[(row-2)*width+2], brow[0]+2, (width-4)*sizeof *image);
    for (g=0; g < 4; g++)
      brow[(g-1) & 3] = brow[g];
  }
  memcpy (image[(row-2)*width+2], brow[0]+2, (width-4)*sizeof *image);
  memcpy (image[(row-1)*width+2], brow[1]+2, (width-4)*sizeof *image);
  free (brow[4]);
  free (code[0][0]);
}

/*
   Patterned Pixel Grouping Interpolation by Alain Desbiolles
*/
void CLASS ppg_interpolate()
{
  int dir[5] = { 1, width, -1, -width, 1 };
  int row, col, diff[2], guess[2], c, d, i;
  ushort (*pix)[4];

  border_interpolate(3);
  if (verbose) fprintf (stderr,_("PPG interpolation...\n"));

/*  Fill in the green layer with gradients and pattern recognition: */
  for (row=3; row < height-3; row++)
    for (col=3+(FC(row,3) & 1), c=FC(row,col); col < width-3; col+=2) {
      pix = image + row*width+col;
      for (i=0; (d=dir[i]) > 0; i++) {
	guess[i] = (pix[-d][1] + pix[0][c] + pix[d][1]) * 2
		      - pix[-2*d][c] - pix[2*d][c];
	diff[i] = ( ABS(pix[-2*d][c] - pix[ 0][c]) +
		    ABS(pix[ 2*d][c] - pix[ 0][c]) +
		    ABS(pix[  -d][1] - pix[ d][1]) ) * 3 +
		  ( ABS(pix[ 3*d][1] - pix[ d][1]) +
		    ABS(pix[-3*d][1] - pix[-d][1]) ) * 2;
      }
      d = dir[i = diff[0] > diff[1]];
      pix[0][1] = ULIM(guess[i] >> 2, pix[d][1], pix[-d][1]);
    }
/*  Calculate red and blue for each green pixel:		*/
  for (row=1; row < height-1; row++)
    for (col=1+(FC(row,2) & 1), c=FC(row,col+1); col < width-1; col+=2) {
      pix = image + row*width+col;
      for (i=0; (d=dir[i]) > 0; c=2-c, i++)
	pix[0][c] = CLIP((pix[-d][c] + pix[d][c] + 2*pix[0][1]
			- pix[-d][1] - pix[d][1]) >> 1);
    }
/*  Calculate blue for red pixels and vice versa:		*/
  for (row=1; row < height-1; row++)
    for (col=1+(FC(row,1) & 1), c=2-FC(row,col); col < width-1; col+=2) {
      pix = image + row*width+col;
      for (i=0; (d=dir[i]+dir[i+1]) > 0; i++) {
	diff[i] = ABS(pix[-d][c] - pix[d][c]) +
		  ABS(pix[-d][1] - pix[0][1]) +
		  ABS(pix[ d][1] - pix[0][1]);
	guess[i] = pix[-d][c] + pix[d][c] + 2*pix[0][1]
		 - pix[-d][1] - pix[d][1];
      }
      if (diff[0] != diff[1])
	pix[0][c] = CLIP(guess[diff[0] > diff[1]] >> 1);
      else
	pix[0][c] = CLIP((guess[0]+guess[1]) >> 2);
    }
}

void CLASS cielab (ushort rgb[3], short lab[3])
{
  int c, i, j, k;
  float r, xyz[3];
  static float cbrt[0x10000], xyz_cam[3][4];

  if (!rgb) {
    for (i=0; i < 0x10000; i++) {
      r = i / 65535.0;
      cbrt[i] = r > 0.008856 ? pow(r,1/3.0) : 7.787*r + 16/116.0;
    }
    for (i=0; i < 3; i++)
      for (j=0; j < colors; j++)
	for (xyz_cam[i][j] = k=0; k < 3; k++)
	  xyz_cam[i][j] += xyz_rgb[i][k] * rgb_cam[k][j] / d65_white[i];
    return;
  }
  xyz[0] = xyz[1] = xyz[2] = 0.5;
  FORCC {
    xyz[0] += xyz_cam[0][c] * rgb[c];
    xyz[1] += xyz_cam[1][c] * rgb[c];
    xyz[2] += xyz_cam[2][c] * rgb[c];
  }
  xyz[0] = cbrt[CLIP((int) xyz[0])];
  xyz[1] = cbrt[CLIP((int) xyz[1])];
  xyz[2] = cbrt[CLIP((int) xyz[2])];
  lab[0] = 64 * (116 * xyz[1] - 16);
  lab[1] = 64 * 500 * (xyz[0] - xyz[1]);
  lab[2] = 64 * 200 * (xyz[1] - xyz[2]);
}

#define TS 512		/* Tile Size */
#define fcol(row,col) xtrans[(row+6) % 6][(col+6) % 6]

/*
   Frank Markesteijn's algorithm for Fuji X-Trans sensors
 */
void CLASS xtrans_interpolate (int passes)
{
  int c, d, f, g, h, i, v, ng, row, col, top, left, mrow, mcol;
  int val, ndir, pass, hm[8], avg[4], color[3][8];
  static const short orth[12] = { 1,0,0,1,-1,0,0,-1,1,0,0,1 },
	patt[2][16] = { { 0,1,0,-1,2,0,-1,0,1,1,1,-1,0,0,0,0 },
			{ 0,1,0,-2,1,0,-2,0,1,1,-2,-2,1,-1,-1,1 } },
	dir[4] = { 1,TS,TS+1,TS-1 };
  short allhex[3][3][2][8], *hex;
  ushort min, max, sgrow, sgcol;
  ushort (*rgb)[TS][TS][3], (*rix)[3], (*pix)[4];
   short (*lab)    [TS][3], (*lix)[3];
   float (*drv)[TS][TS], diff[6], tr;
   char (*homo)[TS][TS], *buffer;

  cielab (0,0);
  ndir = 4 << (passes > 1);
  buffer = (char *) malloc (TS*TS*(ndir*11+6));
  merror (buffer, "xtrans_interpolate()");
  rgb  = (ushort(*)[TS][TS][3]) buffer;
  lab  = (short (*)    [TS][3])(buffer + TS*TS*(ndir*6));
  drv  = (float (*)[TS][TS])   (buffer + TS*TS*(ndir*6+6));
  homo = (char  (*)[TS][TS])   (buffer + TS*TS*(ndir*10+6));

/* Map a green hexagon around each non-green pixel and vice versa:	*/
  for (row=0; row < 3; row++)
    for (col=0; col < 3; col++)
      for (ng=d=0; d < 10; d+=2) {
	g = fcol(row,col) == 1;
	if (fcol(row+orth[d],col+orth[d+2]) == 1) ng=0; else ng++;
	if (ng == 4) { sgrow = row; sgcol = col; }
	if (ng == g+1) FORC(8) {
	  v = orth[d  ]*patt[g][c*2] + orth[d+1]*patt[g][c*2+1];
	  h = orth[d+2]*patt[g][c*2] + orth[d+3]*patt[g][c*2+1];
	  allhex[row][col][0][c^(g*2 & d)] = h + v*width;
	  allhex[row][col][1][c^(g*2 & d)] = h + v*TS;
	}
      }

/* Set green1 and green3 to the minimum and maximum allowed values:	*/
  for (row=2; row < height-2; row++)
    for (min=~(max=0), col=2; col < width-2; col++) {
      if (fcol(row,col) == 1 && (min=~(max=0))) continue;
      pix = image + row*width + col;
      hex = allhex[row % 3][col % 3][0];
      if (!max) FORC(6) {
	val = pix[hex[c]][1];
	if (min > val) min = val;
	if (max < val) max = val;
      }
      pix[0][1] = min;
      pix[0][3] = max;
      switch ((row-sgrow) % 3) {
	case 1: if (row < height-3) { row++; col--; } break;
	case 2: if ((min=~(max=0)) && (col+=2) < width-3 && row > 2) row--;
      }
    }

  for (top=3; top < height-19; top += TS-16)
    for (left=3; left < width-19; left += TS-16) {
      mrow = MIN (top+TS, height-3);
      mcol = MIN (left+TS, width-3);
      for (row=top; row < mrow; row++)
	for (col=left; col < mcol; col++)
	  memcpy (rgb[0][row-top][col-left], image[row*width+col], 6);
      FORC3 memcpy (rgb[c+1], rgb[0], sizeof *rgb);

/* Interpolate green horizontally, vertically, and along both diagonals: */
      for (row=top; row < mrow; row++)
	for (col=left; col < mcol; col++) {
	  if ((f = fcol(row,col)) == 1) continue;
	  pix = image + row*width + col;
	  hex = allhex[row % 3][col % 3][0];
	  color[1][0] = 174 * (pix[  hex[1]][1] + pix[  hex[0]][1]) -
			 46 * (pix[2*hex[1]][1] + pix[2*hex[0]][1]);
	  color[1][1] = 223 *  pix[  hex[3]][1] + pix[  hex[2]][1] * 33 +
			 92 * (pix[      0 ][f] - pix[ -hex[2]][f]);
	  FORC(2) color[1][2+c] =
		164 * pix[hex[4+c]][1] + 92 * pix[-2*hex[4+c]][1] + 33 *
		(2*pix[0][f] - pix[3*hex[4+c]][f] - pix[-3*hex[4+c]][f]);
	  FORC4 rgb[c^!((row-sgrow) % 3)][row-top][col-left][1] =
		LIM(color[1][c] >> 8,pix[0][1],pix[0][3]);
	}

      for (pass=0; pass < passes; pass++) {
	if (pass == 1)
	  memcpy (rgb+=4, buffer, 4*sizeof *rgb);

/* Recalculate green from interpolated values of closer pixels:	*/
	if (pass) {
	  for (row=top+2; row < mrow-2; row++)
	    for (col=left+2; col < mcol-2; col++) {
	      if ((f = fcol(row,col)) == 1) continue;
	      pix = image + row*width + col;
	      hex = allhex[row % 3][col % 3][1];
	      for (d=3; d < 6; d++) {
		rix = &rgb[(d-2)^!((row-sgrow) % 3)][row-top][col-left];
		val = rix[-2*hex[d]][1] + 2*rix[hex[d]][1]
		    - rix[-2*hex[d]][f] - 2*rix[hex[d]][f] + 3*rix[0][f];
		rix[0][1] = LIM(val/3,pix[0][1],pix[0][3]);
	      }
	    }
	}

/* Interpolate red and blue values for solitary green pixels:	*/
	for (row=(top-sgrow+4)/3*3+sgrow; row < mrow-2; row+=3)
	  for (col=(left-sgcol+4)/3*3+sgcol; col < mcol-2; col+=3) {
	    rix = &rgb[0][row-top][col-left];
	    h = fcol(row,col+1);
	    memset (diff, 0, sizeof diff);
	    for (i=1, d=0; d < 6; d++, i^=TS^1, h^=2) {
	      for (c=0; c < 2; c++, h^=2) {
		g = 2*rix[0][1] - rix[i<<c][1] - rix[-i<<c][1];
		color[h][d] = g + rix[i<<c][h] + rix[-i<<c][h];
		if (d > 1)
		  diff[d] += SQR (rix[i<<c][1] - rix[-i<<c][1]
				- rix[i<<c][h] + rix[-i<<c][h]) + SQR(g);
	      }
	      if (d > 1 && (d & 1))
		if (diff[d-1] < diff[d])
		  FORC(2) color[c*2][d] = color[c*2][d-1];
	      if (d < 2 || (d & 1)) {
		FORC(2) rix[0][c*2] = CLIP(color[c*2][d]/2);
		rix += TS*TS;
	      }
	    }
	  }

/* Interpolate red for blue pixels and vice versa:		*/
	for (row=top+3; row < mrow-3; row++)
	  for (col=left+3; col < mcol-3; col++) {
	    if ((f = 2-fcol(row,col)) == 1) continue;
	    rix = &rgb[0][row-top][col-left];
	    c = (row-sgrow) % 3 ? TS:1;
	    h = 3 * (c ^ TS ^ 1);
	    for (d=0; d < 4; d++, rix += TS*TS) {
	      i = d > 1 || ((d ^ c) & 1) ||
		 ((ABS(rix[0][1]-rix[c][1])+ABS(rix[0][1]-rix[-c][1])) <
		2*(ABS(rix[0][1]-rix[h][1])+ABS(rix[0][1]-rix[-h][1]))) ? c:h;
	      rix[0][f] = CLIP((rix[i][f] + rix[-i][f] +
		  2*rix[0][1] - rix[i][1] - rix[-i][1])/2);
	    }
	  }

/* Fill in red and blue for 2x2 blocks of green:		*/
	for (row=top+2; row < mrow-2; row++) if ((row-sgrow) % 3)
	  for (col=left+2; col < mcol-2; col++) if ((col-sgcol) % 3) {
	    rix = &rgb[0][row-top][col-left];
	    hex = allhex[row % 3][col % 3][1];
	    for (d=0; d < ndir; d+=2, rix += TS*TS)
	      if (hex[d] + hex[d+1]) {
		g = 3*rix[0][1] - 2*rix[hex[d]][1] - rix[hex[d+1]][1];
		for (c=0; c < 4; c+=2) rix[0][c] =
			CLIP((g + 2*rix[hex[d]][c] + rix[hex[d+1]][c])/3);
	      } else {
		g = 2*rix[0][1] - rix[hex[d]][1] - rix[hex[d+1]][1];
		for (c=0; c < 4; c+=2) rix[0][c] =
			CLIP((g + rix[hex[d]][c] + rix[hex[d+1]][c])/2);
	      }
	  }
      }
      rgb = (ushort(*)[TS][TS][3]) buffer;
      mrow -= top;
      mcol -= left;

/* Convert to CIELab and differentiate in all directions:	*/
      for (d=0; d < ndir; d++) {
	for (row=2; row < mrow-2; row++)
	  for (col=2; col < mcol-2; col++)
	    cielab (rgb[d][row][col], lab[row][col]);
	for (f=dir[d & 3],row=3; row < mrow-3; row++)
	  for (col=3; col < mcol-3; col++) {
	    lix = &lab[row][col];
	    g = 2*lix[0][0] - lix[f][0] - lix[-f][0];
	    drv[d][row][col] = SQR(g)
	      + SQR((2*lix[0][1] - lix[f][1] - lix[-f][1] + g*500/232))
	      + SQR((2*lix[0][2] - lix[f][2] - lix[-f][2] - g*500/580));
	  }
      }

/* Build homogeneity maps from the derivatives:			*/
      memset(homo, 0, ndir*TS*TS);
      for (row=4; row < mrow-4; row++)
	for (col=4; col < mcol-4; col++) {
	  for (tr=FLT_MAX, d=0; d < ndir; d++)
	    if (tr > drv[d][row][col])
		tr = drv[d][row][col];
	  tr *= 8;
	  for (d=0; d < ndir; d++)
	    for (v=-1; v <= 1; v++)
	      for (h=-1; h <= 1; h++)
		if (drv[d][row+v][col+h] <= tr)
		  homo[d][row][col]++;
	}

/* Average the most homogenous pixels for the final result:	*/
      if (height-top < TS+4) mrow = height-top+2;
      if (width-left < TS+4) mcol = width-left+2;
      for (row = MIN(top,8); row < mrow-8; row++)
	for (col = MIN(left,8); col < mcol-8; col++) {
	  for (d=0; d < ndir; d++)
	    for (hm[d]=0, v=-2; v <= 2; v++)
	      for (h=-2; h <= 2; h++)
		hm[d] += homo[d][row+v][col+h];
	  for (d=0; d < ndir-4; d++)
	    if (hm[d] < hm[d+4]) hm[d  ] = 0; else
	    if (hm[d] > hm[d+4]) hm[d+4] = 0;
	  for (max=hm[0],d=1; d < ndir; d++)
	    if (max < hm[d]) max = hm[d];
	  max -= max >> 3;
	  memset (avg, 0, sizeof avg);
	  for (d=0; d < ndir; d++)
	    if (hm[d] >= max) {
	      FORC3 avg[c] += rgb[d][row][col][c];
	      avg[3]++;
	    }
	  FORC3 image[(row+top)*width+col+left][c] = avg[c]/avg[3];
	}
    }
  free(buffer);
  border_interpolate(8);
}
#undef fcol

/*
   Adaptive Homogeneity-Directed interpolation is based on
   the work of Keigo Hirakawa, Thomas Parks, and Paul Lee.
 */
void CLASS ahd_interpolate()
{
  int i, j, top, left, row, col, tr, tc, c, d, val, hm[2];
  static const int dir[4] = { -1, 1, -TS, TS };
  unsigned ldiff[2][4], abdiff[2][4], leps, abeps;
  ushort (*rgb)[TS][TS][3], (*rix)[3], (*pix)[4];
   short (*lab)[TS][TS][3], (*lix)[3];
   char (*homo)[TS][TS], *buffer;

  if (verbose) fprintf (stderr,_("AHD interpolation...\n"));

  cielab (0,0);
  border_interpolate(5);
  buffer = (char *) malloc (26*TS*TS);
  merror (buffer, "ahd_interpolate()");
  rgb  = (ushort(*)[TS][TS][3]) buffer;
  lab  = (short (*)[TS][TS][3])(buffer + 12*TS*TS);
  homo = (char  (*)[TS][TS])   (buffer + 24*TS*TS);

  for (top=2; top < height-5; top += TS-6)
    for (left=2; left < width-5; left += TS-6) {

/*  Interpolate green horizontally and vertically:		*/
      for (row=top; row < top+TS && row < height-2; row++) {
	col = left + (FC(row,left) & 1);
	for (c = FC(row,col); col < left+TS && col < width-2; col+=2) {
	  pix = image + row*width+col;
	  val = ((pix[-1][1] + pix[0][c] + pix[1][1]) * 2
		- pix[-2][c] - pix[2][c]) >> 2;
	  rgb[0][row-top][col-left][1] = ULIM(val,pix[-1][1],pix[1][1]);
	  val = ((pix[-width][1] + pix[0][c] + pix[width][1]) * 2
		- pix[-2*width][c] - pix[2*width][c]) >> 2;
	  rgb[1][row-top][col-left][1] = ULIM(val,pix[-width][1],pix[width][1]);
	}
      }
/*  Interpolate red and blue, and convert to CIELab:		*/
      for (d=0; d < 2; d++)
	for (row=top+1; row < top+TS-1 && row < height-3; row++)
	  for (col=left+1; col < left+TS-1 && col < width-3; col++) {
	    pix = image + row*width+col;
	    rix = &rgb[d][row-top][col-left];
	    lix = &lab[d][row-top][col-left];
	    if ((c = 2 - FC(row,col)) == 1) {
	      c = FC(row+1,col);
	      val = pix[0][1] + (( pix[-1][2-c] + pix[1][2-c]
				 - rix[-1][1] - rix[1][1] ) >> 1);
	      rix[0][2-c] = CLIP(val);
	      val = pix[0][1] + (( pix[-width][c] + pix[width][c]
				 - rix[-TS][1] - rix[TS][1] ) >> 1);
	    } else
	      val = rix[0][1] + (( pix[-width-1][c] + pix[-width+1][c]
				 + pix[+width-1][c] + pix[+width+1][c]
				 - rix[-TS-1][1] - rix[-TS+1][1]
				 - rix[+TS-1][1] - rix[+TS+1][1] + 1) >> 2);
	    rix[0][c] = CLIP(val);
	    c = FC(row,col);
	    rix[0][c] = pix[0][c];
	    cielab (rix[0],lix[0]);
	  }
/*  Build homogeneity maps from the CIELab images:		*/
      memset (homo, 0, 2*TS*TS);
      for (row=top+2; row < top+TS-2 && row < height-4; row++) {
	tr = row-top;
	for (col=left+2; col < left+TS-2 && col < width-4; col++) {
	  tc = col-left;
	  for (d=0; d < 2; d++) {
	    lix = &lab[d][tr][tc];
	    for (i=0; i < 4; i++) {
	       ldiff[d][i] = ABS(lix[0][0]-lix[dir[i]][0]);
	      abdiff[d][i] = SQR(lix[0][1]-lix[dir[i]][1])
			   + SQR(lix[0][2]-lix[dir[i]][2]);
	    }
	  }
	  leps = MIN(MAX(ldiff[0][0],ldiff[0][1]),
		     MAX(ldiff[1][2],ldiff[1][3]));
	  abeps = MIN(MAX(abdiff[0][0],abdiff[0][1]),
		      MAX(abdiff[1][2],abdiff[1][3]));
	  for (d=0; d < 2; d++)
	    for (i=0; i < 4; i++)
	      if (ldiff[d][i] <= leps && abdiff[d][i] <= abeps)
		homo[d][tr][tc]++;
	}
      }
/*  Combine the most homogenous pixels for the final result:	*/
      for (row=top+3; row < top+TS-3 && row < height-5; row++) {
	tr = row-top;
	for (col=left+3; col < left+TS-3 && col < width-5; col++) {
	  tc = col-left;
	  for (d=0; d < 2; d++)
	    for (hm[d]=0, i=tr-1; i <= tr+1; i++)
	      for (j=tc-1; j <= tc+1; j++)
		hm[d] += homo[d][i][j];
	  if (hm[0] != hm[1])
	    FORC3 image[row*width+col][c] = rgb[hm[1] > hm[0]][tr][tc][c];
	  else
	    FORC3 image[row*width+col][c] =
		(rgb[0][tr][tc][c] + rgb[1][tr][tc][c]) >> 1;
	}
      }
    }
  free (buffer);
}
#undef TS

void CLASS parse_raspberrypi()
{
  //This structure is at offset 0xB0 from the 'BRCM' ident.
  struct brcm_raw_header {
    uint8_t name[32];
    uint16_t width;
    uint16_t height;
    uint16_t padding_right;
    uint16_t padding_down;
    uint32_t dummy[6];
    uint16_t transform;
    uint16_t format;
    uint8_t bayer_order;
    uint8_t bayer_format;
  };
  //Values taken from https://github.com/raspberrypi/userland/blob/master/interface/vctypes/vc_image_types.h
  #define BRCM_FORMAT_BAYER  33
  #define BRCM_BAYER_RAW8    2
  #define BRCM_BAYER_RAW10   3
  #define BRCM_BAYER_RAW12   4
  #define BRCM_BAYER_RAW14   5
  #define BRCM_BAYER_RAW16   6

  struct brcm_raw_header header;
  uint8_t brcm_tag[4];

  // Sanity check that the caller has found a BRCM header
  if (!fread(brcm_tag, 1, sizeof(brcm_tag), ifp) ||
      memcmp(brcm_tag, "BRCM", sizeof(brcm_tag)))
    return;

  width = raw_width;
  data_offset = ftell(ifp) + 0x8000 - sizeof(brcm_tag);

  if(!fseek (ifp, 0xB0-sizeof(brcm_tag), SEEK_CUR) &&
     fread(&header, 1, sizeof(header), ifp)) {
    switch(header.bayer_order) {
      case 0: //RGGB
        filters = 0x94949494;
        break;
      case 1: //GBRG
        filters = 0x49494949;
        break;
      default:
      case 2: //BGGR
        filters = 0x16161616;
        break;
      case 3: //GRBG
        filters = 0x61616161;
        break;
    }

    if (header.format == BRCM_FORMAT_BAYER) {
      switch(header.bayer_format) {
        case BRCM_BAYER_RAW8:
          load_raw = &CLASS load_raw8;
          //1 pixel per byte
          raw_stride = ((header.width + header.padding_right) + 31)&(~31);
          width = header.width;
          raw_height = height = header.height;
          is_raw = 1;
          order = 0x4d4d;
          break;
        case BRCM_BAYER_RAW10:
          load_raw = &CLASS nokia_load_raw;
          //4 pixels per 5 bytes
          raw_stride = (((((header.width + header.padding_right)*5)+3)>>2) + 31)&(~31);
          width = header.width;
          raw_height = height = header.height;
          is_raw = 1;
          order = 0x4d4d;
          break;
        case BRCM_BAYER_RAW12:
          load_raw = &CLASS load_raw12;
          //2 pixels per 3 bytes
          raw_stride = (((((header.width + header.padding_right)*3)+1)>>1) + 31)&(~31);
          width = header.width;
          raw_height = height = header.height;
          is_raw = 1;
          order = 0x4d4d;
          break;
        case BRCM_BAYER_RAW14:
          load_raw = &CLASS load_raw14;
          //4 pixels per 7 bytes
          raw_stride = (((((header.width + header.padding_right)*7)+3)>>2) + 31)&(~31);
          width = header.width;
          raw_height = height = header.height;
          is_raw = 1;
          order = 0x4d4d;
          break;
        case BRCM_BAYER_RAW16:
          load_raw = &CLASS load_raw16;
          //1 pixel per 2 bytes
          raw_stride = (((header.width + header.padding_right)<<1) + 31)&(~31);
          width = header.width;
          raw_height = height = header.height;
          is_raw = 1;
          order = 0x4d4d;
          break;
        default:
          break;
      }
    }
  }
}

/*
   Identify which camera created this file, and set global variables
   accordingly.
 */
void CLASS identify()
{
  char head[32];
  int i, c;
  struct jhead jh;

  flip = filters = UINT_MAX;	/* unknown */
  raw_height = raw_width = cr2_slice[0] = 0;
  maximum = height = width = top_margin = left_margin = 0;
  cdesc[0] = desc[0] = artist[0] = make[0] = model[0] = model2[0] = 0;
  iso_speed = shutter = aperture = focal_len = unique_id = 0;
  thumb_offset = thumb_length = thumb_width = thumb_height = 0;
  load_raw = thumb_load_raw = 0;
  data_offset = meta_offset = meta_length = 0;
  zero_after_ff = dng_version = load_flags = 0;
  timestamp = shot_order = black = 0;
  mix_green = profile_length = data_error = zero_is_bad = 0;
  pixel_aspect = is_raw = raw_color = 1;
  tile_width = tile_length = 0;
  for (i=0; i < 4; i++) {
    cam_mul[i] = i == 1;
    pre_mul[i] = i < 3;
    FORC3 cmatrix[c][i] = 0;
    FORC3 rgb_cam[c][i] = c == i;
  }
  colors = 3;
  for (i=0; i < 0x10000; i++) curve[i] = i;

  order = get2();
  fseek (ifp, 0, SEEK_SET);
  fread (head, 1, 32, ifp);
  if (!memcmp (head,"BRCM",4)) {
    fseek (ifp, 0, SEEK_SET);
    strcpy (make, "RaspberryPi");
    strcpy (model,"Pi");
    parse_raspberrypi();
  }

  if (!is_raw) goto notraw;
  if (!height) height = raw_height;
  if (!width)  width  = raw_width;

  if (!model[0])
    sprintf (model, "%dx%d", width, height);
  if (filters == UINT_MAX) filters = 0x94949494;
  if (thumb_offset && !thumb_height) {
    fseek (ifp, thumb_offset, SEEK_SET);
    if (ljpeg_start (&jh, 1)) {
      thumb_width  = jh.wide;
      thumb_height = jh.high;
    }
  }

  if (!load_raw || height < 22 || width < 22 || colors > 4)
    is_raw = 0;

  if (!cdesc[0])
    strcpy (cdesc, colors == 3 ? "RGBG":"GMCY");
  if (!raw_height) raw_height = height;
  if (!raw_width ) raw_width  = width;
  if (filters > 999 && colors == 3)
    filters |= ((filters >> 2 & 0x22222222) |
		(filters << 2 & 0x88888888)) & filters << 1;
notraw:
  if (flip == UINT_MAX) flip = 0;
}

void CLASS convert_to_rgb()
{
  int row, col, c, i, j, k;
  ushort *img;
  float out[3], out_cam[3][4];
  double inverse[3][3];
  static const double rgb_rgb[3][3] =
  { { 1,0,0 }, { 0,1,0 }, { 0,0,1 } };
  static const double (*out_rgb[])[3] =
  { rgb_rgb };
  static const char *name[] =
  { "sRGB" };
  static const unsigned phead[] =
  { 1024, 0, 0x2100000, 0x6d6e7472, 0x52474220, 0x58595a20, 0, 0, 0,
    0x61637370, 0, 0, 0x6e6f6e65, 0, 0, 0, 0, 0xf6d6, 0x10000, 0xd32d };
  unsigned pbody[] =
  { 10, 0x63707274, 0, 36,	/* cprt */
	0x64657363, 0, 40,	/* desc */
	0x77747074, 0, 20,	/* wtpt */
	0x626b7074, 0, 20,	/* bkpt */
	0x72545243, 0, 14,	/* rTRC */
	0x67545243, 0, 14,	/* gTRC */
	0x62545243, 0, 14,	/* bTRC */
	0x7258595a, 0, 20,	/* rXYZ */
	0x6758595a, 0, 20,	/* gXYZ */
	0x6258595a, 0, 20 };	/* bXYZ */
  static const unsigned pwhite[] = { 0xf351, 0x10000, 0x116cc };
  unsigned pcurve[] = { 0x63757276, 0, 1, 0x1000000 };

  gamma_curve (gamm[0], gamm[1], 0, 0);
  memcpy (out_cam, rgb_cam, sizeof out_cam);
  raw_color |= colors == 1 || document_mode ||
		output_color < 1 || output_color > 6;
  if (!raw_color) {
    oprof = (unsigned *) calloc (phead[0], 1);
    merror (oprof, "convert_to_rgb()");
    memcpy (oprof, phead, sizeof phead);
    if (output_color == 5) oprof[4] = oprof[5];
    oprof[0] = 132 + 12*pbody[0];
    for (i=0; i < pbody[0]; i++) {
      oprof[oprof[0]/4] = i ? (i > 1 ? 0x58595a20 : 0x64657363) : 0x74657874;
      pbody[i*3+2] = oprof[0];
      oprof[0] += (pbody[i*3+3] + 3) & -4;
    }
    memcpy (oprof+32, pbody, sizeof pbody);
    oprof[pbody[5]/4+2] = strlen(name[output_color-1]) + 1;
    memcpy ((char *)oprof+pbody[8]+8, pwhite, sizeof pwhite);
    pcurve[3] = (short)(256/gamm[5]+0.5) << 16;
    for (i=4; i < 7; i++)
      memcpy ((char *)oprof+pbody[i*3+2], pcurve, sizeof pcurve);
    pseudoinverse ((double (*)[3]) out_rgb[output_color-1], inverse, 3);
    for (i=0; i < phead[0]/4; i++)
      oprof[i] = htonl(oprof[i]);
    strcpy ((char *)oprof+pbody[2]+8, "auto-generated by dcraw");
    strcpy ((char *)oprof+pbody[5]+12, name[output_color-1]);
    for (i=0; i < 3; i++)
      for (j=0; j < colors; j++)
	for (out_cam[i][j] = k=0; k < 3; k++)
	  out_cam[i][j] += out_rgb[output_color-1][i][k] * rgb_cam[k][j];
  }

  memset (histogram, 0, sizeof histogram);
  for (img=image[0], row=0; row < height; row++)
    for (col=0; col < width; col++, img+=4) {
      if (!raw_color) {
	out[0] = out[1] = out[2] = 0;
	FORCC {
	  out[0] += out_cam[0][c] * img[c];
	  out[1] += out_cam[1][c] * img[c];
	  out[2] += out_cam[2][c] * img[c];
	}
	FORC3 img[c] = CLIP((int) out[c]);
      }
      else if (document_mode)
	img[0] = img[fcol(row,col)];
      FORCC histogram[c][img[c] >> 3]++;
    }
  if (colors == 4 && output_color) colors = 3;
  if (document_mode && filters) colors = 1;
}

int CLASS flip_index (int row, int col)
{
  if (flip & 4) SWAP(row,col);
  if (flip & 2) row = iheight - 1 - row;
  if (flip & 1) col = iwidth  - 1 - col;
  return row * iwidth + col;
}

void CLASS write_ppm_tiff()
{
  uchar *ppm;
  ushort *ppm2;
  int c, row, col, soff, rstep, cstep;
  int perc, val, total, white=0x2000;

  perc = width * height * 0.01;		/* 99th percentile white level */
  if (!((highlight & ~2) || no_auto_bright))
    for (white=c=0; c < colors; c++) {
      for (val=0x2000, total=0; --val > 32; )
	if ((total += histogram[c][val]) > perc) break;
      if (white < val) white = val;
    }
  gamma_curve (gamm[0], gamm[1], 2, (white << 3)/bright);
  iheight = height;
  iwidth  = width;
  if (flip & 4) SWAP(height,width);
  ppm = (uchar *) calloc (width, colors*output_bps/8);
  ppm2 = (ushort *) ppm;
  merror (ppm, "write_ppm_tiff()");
  if (colors > 3)
    fprintf (ofp,
      "P7\nWIDTH %d\nHEIGHT %d\nDEPTH %d\nMAXVAL %d\nTUPLTYPE %s\nENDHDR\n",
	width, height, colors, (1 << output_bps)-1, cdesc);
  else
    fprintf (ofp, "P%d\n%d %d\n%d\n",
	colors/2+5, width, height, (1 << output_bps)-1);
  soff  = flip_index (0, 0);
  cstep = flip_index (0, 1) - soff;
  rstep = flip_index (1, 0) - flip_index (0, width);
  for (row=0; row < height; row++, soff += rstep) {
    for (col=0; col < width; col++, soff += cstep)
      if (output_bps == 8)
	   FORCC ppm [col*colors+c] = curve[image[soff][c]] >> 8;
      else FORCC ppm2[col*colors+c] = curve[image[soff][c]];
    if (output_bps == 16 && htons(0x55aa) != 0x55aa)
      swab (ppm2, ppm2, width*colors*2);
    fwrite (ppm, colors*output_bps/8, width, ofp);
  }
  free (ppm);
}

int CLASS demo (const char *fp)
{
  int status=0, quality;
  int user_qual=-1;
  const char *bpfile=0, *write_ext;
  char *ofname, *cp;

  raw_image = 0;
  image = 0;
  oprof = 0;
  meta_data = 0;
  ofp = stdout;

  ifname = fp;

    if (!(ifp = fopen (fp, "rb"))) {
      perror (fp);
    }
    status = (identify(),!is_raw);

    write_fun = &CLASS write_ppm_tiff;
    if (!is_raw) goto next;
    shrink = filters && (half_size || ((threshold || aber[0] != 1 || aber[2] != 1)));
    iheight = (height + shrink) >> shrink;
    iwidth  = (width  + shrink) >> shrink;

next:
    if (filters || colors == 1) {
      raw_image = (ushort *) calloc ((raw_height+7), raw_width*2);
      merror (raw_image, "demo()");
    } else {
      image = (ushort (*)[4]) calloc (iheight, iwidth*sizeof *image);
      merror (image, "demo()");
    }
    if (shot_select >= is_raw)
      fprintf (stderr,_("%s: \"-s %d\" requests a nonexistent image!\n"),
	ifname, shot_select);
    fseeko (ifp, data_offset, SEEK_SET);
    (*load_raw)();
    if (document_mode == 3) {
      top_margin = left_margin = 0;
      height = raw_height;
      width  = raw_width;
    }
    iheight = (height + shrink) >> shrink;
    iwidth  = (width  + shrink) >> shrink;
    if (raw_image) {
      image = (ushort (*)[4]) calloc (iheight, iwidth*sizeof *image);
      merror (image, "demo()");
      crop_masked_pixels();
      free (raw_image);
    }
    if (zero_is_bad) remove_zeroes();
    bad_pixels (bpfile);
    if (user_qual >= 0) quality = user_qual;
    if (document_mode < 2)
      scale_colors();
    pre_interpolate();
    if (filters && !document_mode) {
      if (quality == 0)
	lin_interpolate();
      else if (quality == 1 || colors > 3)
	vng_interpolate();
      else if (quality == 2 && filters > 1000)
	ppg_interpolate();
      else if (filters == 9)
	xtrans_interpolate (quality*2-3);
      else
	ahd_interpolate();
    }

    convert_to_rgb();
    write_ext = ".pgm\0.ppm\0.ppm\0.pam" + colors*5-5;
    ofname = (char *) malloc (strlen(ifname) + 64);
    merror (ofname, "demo()");

      strcpy (ofname, ifname);
      if ((cp = strrchr (ofname, '.'))) *cp = 0;
      strcat (ofname, write_ext);
      ofp = fopen (ofname, "wb");
      if (!ofp) {
	    status = 1;
	    perror (ofname);
    	goto cleanup;
      }

    (*write_fun)();
    fclose(ifp);
    if (ofp != stdout) fclose(ofp);
cleanup:
    if (meta_data) free (meta_data);
    if (ofname) free (ofname);
    if (oprof) free (oprof);
    if (image) free (image);

  return status;
}
