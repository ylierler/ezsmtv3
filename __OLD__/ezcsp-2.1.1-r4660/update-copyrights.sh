#! /bin/sh
#
# Updates the copyright messages on all *.cc *.h *.pl files in the current directory.
#

YEAR="`date "+%Y"`"
sed -i -e 's/Copyright Marcello Balduccini \([0-9][0-9][0-9][0-9]\)-[0-9][0-9][0-9][0-9]/Copyright Marcello Balduccini \1-'$YEAR'/' -e 's/Copyright (C) \([0-9][0-9][0-9][0-9]\)-[0-9][0-9][0-9][0-9] Marcello Balduccini/Copyright (C) \1-'$YEAR' Marcello Balduccini/' *.cc *.h *.pl
