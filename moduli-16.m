

// Ambients
k := GF(101);
P2<x,y,z> := ProjectiveSpace(k,2);
R<y0,y1,y2,y3,y4> := PolynomialRing(k,5);

mons2R := Monomials((y0+y1)^2);
mons2S := Monomials((y2+y3+y4)^2);


// Function to construct the Vandermonde matrix
function VanMatrix(pts1, pts2)

    assert #pts1 eq #pts2;
    a := [Eltseq(p) cat [0,0,0] : p in pts1];
    b := [[0,0] cat Eltseq(p) : p in pts2];

    A := Matrix([[Evaluate(mon, p) : mon in mons2R] : p in a]);
    B := Matrix([[Evaluate(mon, p) : mon in mons2S] : p in b]);

    return HorizontalJoin(A,B);
end function;

function VanMatrix2(pts)

    A := Matrix([[Evaluate(mon, p) : mon in mons2R] : p in pts]);
    B := Matrix([[Evaluate(mon, p) : mon in mons2S] : p in pts]);

    return HorizontalJoin(A,B);
end function;


// Function to turn the kernel into a block diagonal tensor.

function KernelToTensor(ker)

    B := Basis(ker);
    K := BaseRing(ker);
    mons := mons2R cat mons2S;
    assert Degree(ker) eq #mons;

    PK := ChangeRing(Parent(mons[1]), K);

    quads := [&+[(PK ! mons[i])*b[i] : i in [1..#mons]] : b in B];

    RP3<x0,x1,x2,x3> := PolynomialRing(K,4);
    vars := [x0,x1,x2,x3];
    
    M := &+[vars[i]*SymmetricMatrix(quads[i]) : i in [1..4]];
    return M;
    
end function;


function MakeCurve(T)

    P := Proj(BaseRing(T));
    A := Submatrix(T, 1, 1, 2, 2);
    B := Submatrix(T, 3, 3, 3, 3);

    return Scheme(P, [Determinant(A), Determinant(B)]);
end function;


//********************************************************************************
// Script.

// Choose a tensor defining a (C, D) pair alla Recillas

P1<s,t> := ProjectiveSpace(k,1);
RP1 := CoordinateRing(P1);

//sqrta := (t^2 - 5*s*t + 12*s^2);

a := t*s^3;
b := t^4 + 2*s^3*t + 16*s^2*t^2 + 2*s^4; 
c := 5*t^4 + t^2*s^2 + t*s^3 + 7*s^4;

/* 
// Different example.
a := t^3*s + 58*t^2*s^2 + 29*t*s^3 + 63*s^4;
b := 10*t^4 + 19*t^2*s^2 + 51*t*s^3 + 8*s^4;
c := 9*t^4 + 11*t^3*s + 5*t^2*s^2 + 10*t*s^3 + 79*s^4;
*/

// Always gives a singular curve.
//a := s^2*t^2;

mat := 91 * Matrix(RP1, [[a, b], [b, c]]);
F := Determinant(mat);

rts, K := PointsOverSplittingField(Scheme(P1, F));
L := ext<K | 2>;


function RootToP4(rt)
    pp := Eltseq(rt);
    mons := [t^2, s*t, s^2];
    sqrta := Sqrt(L ! Evaluate(a, pp));
    return ([sqrta, L ! Evaluate(b, pp)/sqrta] cat
	   [L ! Evaluate(m, pp) : m in mons]);
end function;


p4pts := [RootToP4(r) : r in rts];

M := VanMatrix2(p4pts);
X := MakeCurve(KernelToTensor(NullspaceOfTranspose(M)));

assert IsNonSingular(X);
print Factorization(F);

// Choose 8 points on a conic (y^2-xz)
// pts := [[t^2, t, 1] where  t := k ! i : i in [1..8]];


// Pick a pair of random linear functions
//l1 := x + 3*y + 7*z;
//l2 := 5*x + 11*y + 13*z;

//l1 := x;
//l2 := y;

// Take the image under the random projection
// mp_pts := [[Evaluate(l1, p), Evaluate(l2, p)] : p in pts];


// Check to see if everything is OK

// M := VanMatrix(mp_pts, pts);

