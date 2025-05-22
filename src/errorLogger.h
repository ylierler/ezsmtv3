#ifndef ERROR_LOGGER_H
#define ERROR_LOGGER_H

#include <string>

void logError(std::string errorMessage, int errorCode=1);
void printFileContent(std::string fileName);
void deleteFile(std::string fileName);

#endif