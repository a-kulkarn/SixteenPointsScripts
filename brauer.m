

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
function BrauerGroupDigest(GM, subgroup_list)

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

	// Extract the Brauer group info
	cg := CohomologyGroup(HM, 1);
	Append(~data_list, <Rank(cg), Moduli(cg)>);
    end for;
    
    return data_list;    
end function;


function CreateAbstractWDModule()
    RE := RootSystem("E8");
    WE := ChangeRing(ReflectionGroup(CoxeterGroup(RE)), Integers());

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
end procedure;
