# first parameter - Coq version, second, - build version (can be empty)
# note that building images with compilers require copying the Liquidity compliler executable located in the in this folder; for that reason, the docker context should be this folder and not the subfolders.

docker build -t aucobra/concert:deps-$1$2 -f ConCert-deps-$1/Dockerfile .
docker build -t aucobra/concert:deps-$1-with-compilers$2 -f ConCert-deps-$1-with-compilers/Dockerfile .
