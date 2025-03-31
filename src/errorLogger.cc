#include "errorLogger.h"
#include <string>
#include <glog/logging.h>

void logError(std::string errorMessage, int errorCode) {
    if (VLOG_IS_ON(2)) {
        LOG(FATAL) << errorMessage;
    }
    LOG(ERROR) << errorMessage;
    exit(errorCode);
}