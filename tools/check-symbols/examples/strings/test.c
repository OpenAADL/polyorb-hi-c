/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://ocarina.enst.fr
 *
 * Copyright (C) 2008, GET-Telecom Paris.
 */

#include <string.h>

int main( int argc , char *argv[] )
{
		char str[512];

		memset ( str , '\0' , 512 );
		strncpy( str , "bonjour" , 6 );

		printf ( "%s" , str );

		return (0);
}
