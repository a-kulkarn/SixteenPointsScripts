

k := GF(101);
R<x0,x1,x2,x3> := PolynomialRing(k, 4);
P3 := Proj(R);

A := SymmetricMatrix(R, [0,0,0,0,1/2,0]);
B := SymmetricMatrix(R, [1,0,86,0,0,24]);
C := SymmetricMatrix(R, [0,0,0,0,-51,0]);
D := SymmetricMatrix(R, [0,0,1,-1/2,0,0]);

AA := x0*A + x1*B + x2*C + x3*D;

X3 := Scheme(P3, Determinant(AA));
X2 := Scheme(P3, x1^2-x0*x2);
X := X2 meet X3;
assert IsNonsingular(X);
