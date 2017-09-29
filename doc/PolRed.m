/*******************************************************************************
           AN ALGORITHM FOR REDUCING NUMBER-FIELD DEFINING POLYNOMIALS
                   IMPLEMENTED BY ALEXANDRE GÉLIN - LIP6/UPMC
*******************************************************************************/

//input must be a polynomial in 'x'
P<x>:=PolynomialRing(RationalField());

//for considering only one conjugate of complex roots.
PosRoot:=function(pos,r1)
    if pos le r1 then
	return pos;
    end if;
    return r1+(pos+1-r1) div 2;
end function;

//build the weighted lattices
MatBuild:=function(M0,weights,Dim,r1)
    M:=M0;
    for j in [j : j in [1..Dim] | weights[PosRoot(j,r1)] ne 1] do 
	K:=1/weights[PosRoot(j,r1)];
	for i in [1..Dim] do
	    M[i,j]:=K*M0[i,j];
	end for;
    end for;
    return M;
end function;

//avoid useless vectors in the enumeration
NextVect:=function(SV,M,Epsilon)
    while not IsEmpty(SV) do
	sv:=NextVector(SV);
	if Abs(sv[1]*M[1,2]-sv[2]*M[1,1]) lt Epsilon then
	    sv:=NextVector(SV);
	else return sv;
	end if;
    end while;
    return NextVector(SV);
end function;

//Recover a polynomial from real approximations
Poly:=function(weights,Wvect,r1,r2,Dim,RFp)
    S2:=1/Sqrt(RFp!2);
    Px:=PolynomialRing(RFp);
    poly:=1;
    for i in [1..r1] do
	poly*:=(Px.1-weights[i]*Wvect[i]);
    end for;
    for i in [1..r2] do
	t:=S2*weights[r1+i];
	poly*:=(Px.1^2 - 2*t*Wvect[r1+2*i-1]*Px.1 +
		t^2*(Wvect[r1+2*i-1]^2+Wvect[r1+2*i]^2));
    end for;
    Coeffs:=Coefficients(poly);
    return P![Round(Coeffs[i]) : i in [1..Dim+1]];
end function;

MaxCoeff:=function(Pol)
    return Max([Abs(c) : c in Coefficients(Pol)]);
end function;

EnumLat:=function(M0,weights,Dim,r1,r2,MCf,RFp,Epsilon)
    Mcf:=MCf;
    M:=MatBuild(M0,weights,Dim,r1);
    try Lat:=LatticeWithBasis(M);
    catch e str:=Sprint(1+Floor(Log(2,Precision(RFp))));
	    print "Increase precision to 2^" cat str cat " for completeness";
	    return 0,MCf,0;
    end try;
    SV:=ShortVectorsProcess(Lat,Dim);
    Wvect:=NextVect(SV,M,Epsilon);
    while not Norm(Wvect) eq 0 do
	Polt:=Poly(weights,Wvect,r1,r2,Dim,RFp);
	if IsIrreducible(Polt) then
	    MCt:=MaxCoeff(Polt);
	    if MCt lt Mcf then Polf:=Polt; Mcf:=MCt; vec:=Wvect; end if;
	end if;
	Wvect:=NextVect(SV,M,Epsilon);
    end while;
    if Mcf eq MCf then return 0,MCf,0; end if;
    return Polf,Mcf,vec;
end function;

PolRed:=function(Pol,c : Prec:=2^6,Proof:=false,Var:=false)
    Dim:=Degree(Pol);
    NF:=NumberField(Pol);
    O:=MaximalOrder(NF);
    r1,r2:=Signature(NF);
    r:=r1+r2;
    Disc:=Abs(Discriminant(O));
    bool:=false;
    repeat try M0:=BasisMatrix(MinkowskiLattice(O:Precision:=Prec)); bool:=true;
	   catch e Prec*:=2; end try;
    until bool;
    RFp:=RealField(Prec);
    Epsilon:=Sqrt(RFp!1/10^Prec);
    Polf:=0;
    MCf:=Disc;
    k:=0;
    logs:=[0 : i in [1..r]]; weights:=[1 : i in [1..r]];
    while Polf cmpeq 0 or (Proof eq true and k lt Log(c,MaxCoeff(Polf))+Dim) do
	pos:=r; lvlin:=true; sum:=0;
	while pos le r do //enumeration of the lattices
	    if pos eq 1 then
		logs[1]:=k-sum;
		if r1 eq 0 then logs[1]:=logs[1] div 2; end if;
		weights[1]:=c^logs[1];
		Polt,MCt,vect:=EnumLat(M0,weights,Dim,r1,r2,MCf,RFp,Epsilon);
		if MCt lt MCf then Polf:=Polt; MCf:=MCt; vecf:=vect; end if;
		pos+:=1;
		lvlin:=false;
	    else
		if lvlin then
		    logs[pos]:=0; weights[pos]:=1;
		    pos-:=1;
		else
		    logs[pos]+:=1; weights[pos]*:=c;
		    if pos gt r1 then sum+:=2; else sum+:=1; end if;
		    if sum gt k then
			if pos gt r1 then sum-:=2*logs[pos];
			else sum-:=logs[pos]; end if;
			pos+:=1;
		    else
			pos-:=1;
			lvlin:=true;
		    end if;
		end if;
	    end if;
	end while;
	if r1 eq 0 then k+:=2; else k+:=1; end if;
    end while;
    //if the variable change is required
    if Var then return Polf,Coordinates(vecf); end if;
    return Polf;
end function;
