// Compile with: g++ test-main.cc common.cc phpemu.cc

#include <stdlib.h>
#include <sys/wait.h>

#include <iostream>
#include <fstream>

#include <string>
#include <vector>

#include "phpemu.h"

#include "common.h"

using namespace std;

class myexception: public exception
{
  virtual const char* what() const throw()
  {
    return "My exception happened";
  }
} myex;


int main(void)
{

	string x;
	

	x="hi";
	
	cout << x << endl;
	
	x=" babe";
	
	cout << x << endl;
	
	x=x+" babe";
	
	cout << x << endl;

	ifstream ifs("mylib.cc"); //,ifstream::in);
	if (ifs.fail())
	{	cout << "***Unable to open q.cc. Aborting." << endl;
	
		exit(1);
	}

	while(!ifs.eof())
	{	getline(ifs,x);

		vector<string> matches;

		bool f;

		f=preg_match("^\\#include <(.*)>",x,matches);
		
		if (f)
		{	cout << "line: " << x << endl;
			for(int i=1;i<matches.size();i++)
				cout << i << ") " << matches[i] << endl;
			cout << endl;
		}
	}

	ifs.close();

	x="at(123),at(9876)";
	cout << "before: " << x << endl;
	x=preg_replace("([0-9][0-9]*)","S\\1E",x);
	cout << "after: " << x << endl;

	int res;
	
	res=system("grep \"hi\" mylib.cc");
	
	cout << "res=" << WEXITSTATUS(res) << endl;

	x="hi baby baby";
	x=str_replace("ab","ba",x);
	cout << x << endl;

	cout << preg_quote("a.s+df*g") <<endl;

	x="asdfg \n\r";
	cout << "\"" << rtrim(x,"\r\n") << "\"" << endl;
	x="  asdfg";
	cout << "\"" << ltrim(x) << "\"" << endl;
	x="  asdfg  \r\n";
	cout << "\"" << trim(x) << "\"" << endl;

	try
	{	throw myexception();
	}
	catch(int e)
	{	cout << "got it " << e << endl;
	}
	catch(exception e)
	{	cout << "exc" << endl;
	}
	catch(...)
	{	cout << "default" << endl;
	}

	cout << date() << endl;

	exit(0);
}
