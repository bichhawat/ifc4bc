/*
 *  Logger.h
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 7/14/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#ifndef Logger_h
#define Logger_h

#include <time.h>
#include <vector>

namespace JSC {
	
	class Logger {
		
	private:
		static Logger* s_logger;
		FILE * pFile;
		time_t rawtime;
		
	public:
		Logger();
		Logger(Logger const&);
		Logger& operator = (Logger const&);
		static Logger& logger();
		
		void log(const char*);
		//void log(const char**);
		void log(std::vector<const char*>&);
		~Logger();
		
	};
}

#endif // Logger_h
