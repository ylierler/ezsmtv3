#include "errorLogger.h"
#include <string>
#include <glog/logging.h>
#include <boost/filesystem.hpp>
#include <fstream>
#include <iostream>

using namespace std;

void printFileContent(std::string fileName) {
  boost::filesystem::path file = fileName;
  if (boost::filesystem::exists(file)) {
    std::ifstream printFile(fileName);
    if (printFile.is_open()) {
      std::string line;
      while (getline(printFile, line)) {
        std::cout << line << endl;
      }
      printFile.close();
    }
  }
}

void deleteFile(std::string fileName) {
  boost::filesystem::path file = fileName;
  if (boost::filesystem::exists(file)) {
    if (remove(fileName.c_str()) == 0) {
      VLOG(3) << "File '" << fileName << "' deleted successfully." << std::endl;
    }
  }
}

void logError(std::string errorMessage, int errorCode) {
    if (VLOG_IS_ON(2)) {
        LOG(FATAL) << errorMessage;
    }
    LOG(ERROR) << errorMessage;
    exit(errorCode);
}