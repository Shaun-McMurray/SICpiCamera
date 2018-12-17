#include <opencv2/opencv.hpp>
#include <opencv2/imgcodecs.hpp>
#include <opencv2/highgui.hpp>
#include <opencv2/imgproc.hpp>
#include <iostream>
#include <fstream>
#include <iomanip>
using namespace cv;
using namespace std;

int IMAGE_WIDTH = 640;
int IMAGE_HEIGHT = 480;
Mat matread(const string& filename);

int main(int argc, char** argv)
{
    auto startFile = chrono::steady_clock::now();

	CommandLineParser parser(argc, argv, "{@input | ../stuff.raw | input image}");

    FILE *fp = NULL;
    char *imagedata = NULL;
    int framesize = IMAGE_WIDTH * IMAGE_HEIGHT;
    
    fp = fopen(parser.get<String>("@input").data(), "rb");

    imagedata = (char*) malloc (sizeof(char) * framesize);
    fread(imagedata, sizeof(char), framesize, fp);   

    Mat img = Mat(IMAGE_HEIGHT, IMAGE_WIDTH, CV_8UC1);
    memcpy(img.data, imagedata, framesize);

    if (img.empty()) 
    {
        std::cerr << "Could not open file" << std::endl; 
        return 1;
    }

    free(imagedata);
    fclose(fp);

    Mat decoded = imdecode(img, 0);
    if (!decoded.data) 
    {
        std::cerr << "Decoded matrix empty" << std::endl; 
        return 1;
    }

    Mat RG2BGR_EA, HSV; 
    
    cvtColor(decoded, RG2BGR_EA, COLOR_BayerRG2BGR_EA, 0);
    cvtColor(RG2BGR_EA, HSV, COLOR_BGR2HSV, 1);

    imshow("RG2BGR_EA", RG2BGR_EA);
    imshow("HSV", HSV);

    waitKey(0);

    return 0;
}
