/*
 *  URLMap.cpp
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 7/7/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#include "URLMap.h"
#include "config.h"
#include <stdio.h>

namespace JSC {
	
	URLMap* URLMap::s_map = NULL; // initialize pointer
	    
	URLMap::URLMap() {
		map = new URLEntry*[MAP_SIZE]; // create our "map"
        policyArray = new char*[100];
		for (int i = 0; i < MAP_SIZE; i++) { // initialize map
			map[i] = NULL;
		};
		idx = 2; // initialize the current index
		// these are put manually for quick initialization and to avoid filter exceptions
		map[0] = new URLEntry("policy", 1); // fallback given when map is full
		map[1] = new URLEntry("NULL", 0); // create generic value for NULL urls
        map[2] = new URLEntry("secret", 2); // User-taint - label is 2 and pLabel is 0
		lastIdx = 0;
		setLast(2); // initialize the last label
	}
	
	URLMap& URLMap::urlmap() {
		if (s_map == NULL) { // is this the first call?
			s_map = new URLMap(); // create sole instance
		}
		return *s_map; // return pointer to instance
	}	
	
	// -----------Private----------- //
	
	void URLMap::append(const char* url, bool isPolicy) { // append url to map
		// NOTE: any call to append should check capacity() first
		if(isPolicy)
        {
            policyArray[policyCount] = strdup(url);
            policyCount++;
        }
        else{
            // append url to map
            // NOTE: any call to append should check capacity() first
            idx++; // move current map lcoation
            map[idx] = new URLEntry(url, (uint64_t)1<<(idx-1)/*, (uint64_t)1<<(idx-1)*/); // set map head to new URLEntry
            setLast(idx);
        }
	}
	
	int URLMap::search(const char* url) { // is the url already in the map?
		for (int i = idx; i >= 0; i--) { // iterate from current index backwards
            int index = strcmp(map[i]->getURL(), url);
			if (index == 0) { // is it this one?
				return i; // return url index
			}
            else if (index < 0) {
                int length = strlen(map[i]->getURL());
                int urlLength = strlen(url);
                if (length > urlLength) {
                    char* str = new char[length];
                    strncpy(str, url, length);
                    if (strcmp(map[i]->getURL(), url) == 0)
                        return i;
                }
            }
		}
		return OUT_OF_BOUNDS; // if the url isn't in the map
	}
	
	const char* URLMap::filter(const char* url) { // not implemented, for later use
		char str[5]; // create temporary string
        char str1[3];
		strncpy(str, url, 4); // set the string
		str[4] = '\0';
        strncpy(str1, url, 2);
		if (strcmp(str, "file") == 0 || strcmp(str, "http") == 0 || strcmp(str, "Inte") == 0 ||
            strcmp(str, "read") == 0 || strcmp(str, "unkn") == 0 || strcmp(str1, "//") == 0) { // what's the urls origin?
			return url;
		}
        else if (strcmp(str, "NULL") == 0 || strcmp(str, "") == 0 || strcmp(str, "abou") == 0){
            return "NULL";
        }
		else { // this could potentially become recursive
            return "!";
            // Original
			// return "NULL";
		}
	}
	
	void URLMap::setLast(int i) {
		if (lastIdx != i) {
			lastIdx = i;
			uint64_t temp = map[lastIdx]->getValue().Val();
            // uint64_t temp1 = map[lastIdx]->getValue().pLabel;
			lastLabel = JSLabel(temp);
		}
	}
	
	// -----------Public----------- //
	
	void URLMap::put(const char* url, bool isPolicy) { // put url on map
        //readPolicy();
        bool isPresent = false;
        if (isPolicy) {
            for (int i = 0; i < policyCount; i++) {
                // printf("fdsgdgd %s\n", policyArray[i]);
                if (strcmp(policyArray[i], url) == 0) {
                    isPresent = true;
                    break;
                }
            }
            if (!isPresent) {
                append(url, isPolicy);
            }
        }
        else {
            if (strncmp(url, "secret", 6) != 0)
                url = strdup(filter(url));
            // Extract the domain from the URL
            char* domain = new char[strlen(url)];
            
            if (strncmp(url, "http:", 5) == 0) {
                sscanf(url, "http://%[^/]", domain);
            }
            else if (strncmp(url, "https", 5) == 0) {
                sscanf(url, "https://%[^/]", domain);
            }
            else if (strncmp(url, "//", 2) == 0) {
                sscanf(url, "//%[^/]", domain);
            }
            else {
                strcpy(domain, url);
            }
            strcpy(domain, url);
            // ---------------------------------
//            int i = 0;
//            if (strcmp(domain, "ssl.bbc.co.uk") == 0 ||
//                strcmp(domain, "static.bbc.co.uk") == 0 || strcmp(domain, "fig.bbc.co.uk") == 0 ||
//                strcmp(domain, "sa.bbc.co.uk") == 0 || strcmp(domain, "ssa.bbc.com") == 0)
//            {
//                i = search("ssl.bbc.com");
//            }
//            else {
//                i = search(domain);
//            }
            int loc = search(domain);
            //
            if (loc == OUT_OF_BOUNDS) { // if the url's not in the map add it
                if (capacity()) { // is the map full?
                    append(domain, isPolicy);
                } else { //TODO: remove this or comment after debug
                    printf("Map full in URLMap.cpp?\n");
                }
            } else {
                // setLast(loc);
            }
        }
	}
    
    void URLMap::readPolicy() 
    {
        FILE *ifp, *ofp;
        char *mode;
        mode = strdup("r");
        char top[9];  /* One extra for nul char. */
        char bottom[9];
        
        ifp = fopen("/Users/fcs-user/Git/for-jinank/IFC/PasswordStrength/test.txt", mode);
        
        if (ifp == NULL) {
            fprintf(stderr, "Can't open input file in.list!\n");
            exit(1);
        }
        
        while (fscanf(ifp, "%s %s", top, bottom) == 2) {
            fprintf(ofp, "%s %s\n", top, bottom);
        }
        
        fclose(ifp);
    }
	
	JSLabel URLMap::getLabel(const char* url) { // get label for given url
		
        for (int i = 0; i < policyCount; i++)
        {
            if (strcmp(policyArray[i], url) == 0) 
                return map[0]->getValue();
        }

        if(strncmp(url, "secret", 6) != 0)
            url = strdup(filter(url));
        // Extract the domain from the URL
        char* domain = new char[strlen(url)];
        if (strstr(url, "review") != NULL) {
            strcpy(domain, url);
        }
        else if (strncmp(url, "http:", 5) == 0)
        {
            sscanf(url, "http://%[^/]", domain);
        }
        else if (strncmp(url, "https", 5) == 0)
        {
            sscanf(url, "https://%[^/]", domain);
        }
        else if (strncmp(url, "//", 2) == 0) {
            sscanf(url, "//%[^/]", domain);
        }
        else
        {
            strcpy(domain, url);
        }
        strcpy(domain, url);
        // ---------------------------------
//        int i = 0;
//        if (strcmp(domain, "ssl.bbc.co.uk") == 0 || strcmp(domain, "static.bbc.co.uk") == 0 || strcmp(domain, "fig.bbc.co.uk") == 0 ||
//            strcmp(domain, "sa.bbc.co.uk") == 0 || strcmp(domain, "ssa.bbc.com") == 0)
//        {
//            i = search("ssl.bbc.com");
//        }
//        else {
//            i = search(domain);
//        }
        int i = search(domain);
		if (i == OUT_OF_BOUNDS) { // add to map and return value
			if (capacity()) { // is the map full?
				append(domain, false);
				return head();
			} else { // return the fallback value
				return map[1]->getValue(); 
			}
		} else { // return value from list
			return map[i]->getValue();
		}
	}
	
	JSLabel URLMap::head() { // returns head of map
		return map[idx]->getValue();
	}
	
	char * URLMap::sHead() {
		char* temp = 0;
		sprintf(temp,  "%" PRIu64, URLMap::urlmap().head().Val());
		return temp;
	}
	
	JSLabel URLMap::lastAsLabel() {
		return lastLabel;
	}
	
	uint64_t URLMap::lastAsVal() {
		return lastLabel.Val();
	}
	
	URLMap::~URLMap() { // deconstructor
		for (int i = idx; i >= 0; i--) { // delete non null entries
			delete map[i];
		}
		delete[] map; // delete the map :(
	}
	
}
