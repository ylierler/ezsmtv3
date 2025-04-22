{apartment(1..2)} = 1.
distance(1,4). rent(1,170).
distance(2,2). rent(2,140).
#minimize{Y/Z@2,X : apartment(X), rent(X,Y), distance(X,Z)}.