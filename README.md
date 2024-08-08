
to install use
g++ rbse.cpp -o rbse

works on pairs of qcnf and qrc with same name e.g.
example.qcnf example.qrp

to run use
./rbse <qrpfilenamebeforeextension> -o <outputname>

e.g ./rbse example -o contradiction
will generate contradiction.cnf
