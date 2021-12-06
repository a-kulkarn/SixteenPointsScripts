

//**************************************************************************************
// Functions
//**************************************************************************************

// Given a Galois Module GM, return the list of possible H1s we can get from restriction.
function PossibleGaloisModules(GM, subgroup_list)

    WD := Group(GM);
    data_list := [];
    i := 1;
    for H in subgroup_list do
	if H`order eq 1 then
	    continue;
	end if;
	
	Hgrp := sub<WD | [WD ! g : g in Generators(H`subgroup)]>;
	UM := Restriction(GM, Hgrp);
	HM := CohomologyModule(Hgrp, UM);

	Append(~data_list, HM); // We can recover the group via Group(...)
    end for;
    
    return data_list;
end function;

function BrauerGroups(data_list)
    return [<Rank(cg), Moduli(cg)> where cg := CohomologyGroup(M,1) : M in data_list];
end function;


// Records a digested list of the first cohomology groups.
function BrauerGroupDigest(GM, subgroup_list : RecordFormat:=true)

    WD := Group(GM);
    data_list := [];
    i := 1;
    for H in subgroup_list do
	if RecordFormat and H`order eq 1 then
	    continue;
	elif not RecordFormat and Order(H) eq 1 then
	    continue;
	end if;

	if RecordFormat then
	    Hgrp := sub<WD | [WD ! g : g in Generators(H`subgroup)]>;
	else
	    Hgrp := sub<WD | [WD ! g : g in Generators(H)]>;
	end if;
	
	UM := Restriction(GM, Hgrp);
	HM := CohomologyModule(Hgrp, UM);

	// Extract the Brauer group info
	cg := CohomologyGroup(HM, 1);
	Append(~data_list, <Rank(cg), Moduli(cg)>);
    end for;
    
    return data_list;    
end function;


function CreateAbstractWDModule()
    RE := RootSystem("E8");
    CG := CoxeterGroup(RE);
    RG, mp := ReflectionGroup(CG);
    WE := ChangeRing(RG, Integers());

    // There is one conjugacy class of subgroups of index 135. This is the one corresponding
    // to fixing an even 2-torsion class. As it happens, this is the Weyl Group for a D8
    // subsystem.

    subs := Subgroups(WE : IndexEqual:=135);
    assert #subs eq 1;
    WD := subs[1]`subgroup;

    // Construct the Galois Module
    GM := GModule(WD);

    return WD, GM;
end function;

function MapToE8ReflectionGroup()
    RE := RootSystem("E8");
    CG := CoxeterGroup(RE);
    RG, mp := ReflectionGroup(CG);
    return Inverse(mp);
end function;


////////////////////////
// Look for transitive subgroups

function IsTransitiveOnRoots(mp, H, d8roots)
    // We need to provide a map `mp` back to a permutation group.
    // We need to also give the orbit of D8 roots.
    
    if Order(H) eq 1 then
	return false;
    end if;

    HC := sub<Codomain(mp)| [mp(h) : h in Generators(H)]>;

    if d8roots in Orbits(HC) then
	return true;
    else
	return false;
    end if;
end function;


////////////////////////
// Loading and saving
procedure MakeAndSaveSubgroups(WD)
    anch := Time();
    subgroups := Subgroups(WD);
    elapsedT  := Time(anch);
    Write("WD8_gal_mods", subgroups, "Magma" : Overwrite:=true);
    Write("subgroups_timing", elapsedT);
end procedure;


function LoadData()
    subgroups := eval Read("WD8_gal_mods");
    WD := ChangeRing(subgroups[#subgroups]`subgroup, Integers());
    GM := GModule(WD);
    return WD, GM, subgroups;
end function;


////////////////////////
// Main script

procedure Main()
    try
	WD, GM, subgroups := LoadData();
    catch e
	WD, GM := CreateAbstractWDModule();
	MakeAndSaveSubgroups(WD);
	WD, GM, subgroups := LoadData();
    end try;

    bgroups := BrauerGroupDigest(GM, subgroups);

    print "Brauer groups that are possible:";
    print Set(bgroups);

    print "Smallest group actions for each Brauer group.";
    for BG in Set(bgroups) do
	// We need to add one to the index since the trivial group gets deleted.
	print subgroups[Index(bgroups, BG)+1];
    end for;
end procedure;

procedure TransitiveCheck()
    // Version of main to only look at subgroups which act on the standard set of size 16 transitively.
    
    WD, GM, subgroups := LoadData();

    // Construct the permutation representation of degree 16 and an identification
    WP := WreathProduct(Sym(2), Sym(8));
    index_two_subgroups := Subgroups(WP : IndexEqual:=2);

    isiso := [G`subgroup : G in index_two_subgroups | IsIsomorphic(G`subgroup, WD)];
    assert #isiso eq 1;
    WP := isiso[1];
    _, mp := IsIsomorphic(WP, WD);

    // Fetch the transitive subgroups
    tsubs := [H`subgroup : H in Subgroups(WP : IsTransitive:=true)];
    tsubsinWD := [sub<WD | [mp(h) : h in Generators(H)]> : H in tsubs];

    bgroups := BrauerGroupDigest(GM, tsubsinWD : RecordFormat:=false);

    print "Brauer groups that are possible for transitive groups:";
    print Set(bgroups);
    
end procedure;
