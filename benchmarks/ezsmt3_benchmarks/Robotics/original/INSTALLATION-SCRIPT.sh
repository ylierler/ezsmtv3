#! /bin/sh
#

cd $HOME
mkdir SOLVERS

wget "http://www.mbal.tk/ezcsp/ezcsp-1.7.9-r4024.tgz"
wget "http://www.mbal.tk/ezcsp/dlv_rsig-1.8.10.tgz"
wget "http://www.mbal.tk/mkatoms/Source/mkatoms-2.16.tgz"
wget "https://sourceforge.net/projects/potassco/files/clasp/3.1.3/clasp-3.1.3-x86_64-linux.tar.gz/download"
mv download clasp-3.1.3-x86_64-linux.tar.gz
wget "https://sourceforge.net/projects/potassco/files/gringo/3.0.5/gringo-3.0.5-amd64-linux.tar.gz/download"
mv download gringo-3.0.5-amd64-linux.tar.gz
wget "https://d37drm4t2jghv5.cloudfront.net/distributions/24.5.6/linux/linux_x64_64_sfx.exe"

tar -zxf dlv_rsig-1.8.10.tgz
tar -zxf ezcsp-1.7.9-r4024.tgz
tar -zxf mkatoms-2.16.tgz
tar -zxf gringo-3.0.5-amd64-linux.tar.gz
tar -zxf clasp-3.1.3-x86_64-linux.tar.gz

cd gringo-3.0.5-amd64-linux
cp gringo $HOME/bin/
chmod a+rx $HOME/bin/gringo

cd ../clasp-3.1.3
cp clasp-3.1.3-x86_64-linux $HOME/bin/clasp
chmod a+rx $HOME/bin/clasp
cd ../

cd mkatoms-2.16
./configure --help
./configure --prefix $HOME
make
make install
cd ../

cd dlv_rsig-1.8.10
./configure --prefix $HOME
make
make install
cd ../

cd ezcsp-1.7.9-r4024
env CFLAGS="-I$HOME/include/" CXXFLAGS="-I$HOME/include/" LDFLAGS="-L$HOME/lib/" ./configure --prefix $HOME
make
make install
cd ../

chmod a+rx linux_x64_64_sfx.exe
./linux_x64_64_sfx.exe
cd $HOME/bin
ln -s $HOME/SOLVERS/gams24.5_linux_x64_64_sfx/gams .

echo "All executables are ready in $HOME/bin"
