/*
 *  Logger.cpp
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 7/14/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#include "config.h"
#include "Logger.h"

namespace JSC {
	
	Logger* Logger::s_logger = NULL; // initilaize pointer
	
	Logger::Logger() {
		pFile = fopen("/Users/alancleary/dev/reu/webkit/logfile.txt", "w");
		time(&rawtime);
		fprintf(pFile, "log file created on %s\n-------------------------\n\n", ctime(&rawtime));
		//log(std::vector<const char*>(){"log file from ", ctime(&rawtime), "\n-------------------------\n\n"};
		//char* temp[] = {"log file from ", ctime(&rawtime), "\n-------------------------\n\n"}
		//log(temp);
	}
	
	Logger& Logger::logger() {
		if (s_logger == NULL) {
			s_logger = new Logger();
		}
		return *s_logger;
	}

	void Logger::log(const char* str) {
		fprintf(pFile, "%s", str);
		fflush(pFile);
	}
	
	/*
	void Logger::log(const char** arr) {
		int len = sizeof(arr);
		for (int i = 0; i < len; i++) {
			fprintf(pFile, "%s", arr[i]);
		}
		fflush(pFile);
	}
	*/

	void Logger::log(std::vector<const char*>& vec) {
		int len = vec.size();
		for (int i = 0; i < len; i++ ) {
			fprintf(pFile, "%s", vec[i]);
		}
		fflush(pFile);
	}

	Logger::~Logger() {
		fprintf(pFile, "\n\n-------------------------\nlog file session ended at %s\n\n\n", ctime(&rawtime));
		//log(new std::vector<const char*> ("\n\n-------------------------\nlog file ended at ", ctime(&rawtime), "\n\n");
		//log("ending log session");
		//log("time:");
		//log(ctime(&rawtime));
		fclose(pFile);
	}
}
