-- Macaulay2 function to compute the spreading number recursively 
-- v0.1
-- Ben Babcock <bababcoc@lakeheadu.ca>
--------------------------------------------------------------------------------

recursive_spread = {nMinusOne => {}, dMinusTwo => {} } >> opts -> (n,d) -> (
    R := QQ[x_1..x_n];
    use R;

    -- If n = 1 or d = 1, then spreading number is 1, and the maximum
    -- independent set is just {x_1^d}.
    if n == 1 or d == 1 then return(set {x_1^d});

    -- If d = 2, then the spreading number is n, and the maximum independent set
    -- is just {x_1^2,..x_n^2}
    if d == 2 then (
	nset := {};
	for i from 1 to n do (nset = append(nset, x_i^2));
	return(set nset);
    );

    -- Otherwise, we need the maximum independent sets for S_n(d - 2),
    -- S_{n-1}(d).  These may be supplied as optional input; otherwise, we 
    -- will recurse to obtain them.
    x1sq := {};
    nox1 := {};

    if (#opts.nMinusOne > 0 and #opts.dMinusTwo > 0) then (
	x1sq = set opts.dMinusTwo;
	nox1 = set opts.nMinusOne;
    )
    else (
	x1sq = recursive_spread(n, d - 2);
	nox1 = recursive_spread(n - 1, d);
    );

    -- We need to adjust the elements in each of these sets.
    -- The elements of x1sq need to be increased by a factor of x_1^2, and the
    -- elements of nox1 need to have their indices shifted by +1.
    use R;
    x1sq = set apply(toList x1sq, i -> sub(i,R)*(x_1^2));
    nox1 = set apply(toList nox1, i -> liftVars(i,R));

    -- This is the "candidate" maximum independent set for S_n(d).
    candidate := x1sq + nox1;

    -- Now we construct S_n(d) and find all vertices that are not in the 
    -- candidate set--this is our "buffer" set.
    k := binomial(d + n - 1, n - 1);
    S := QQ[z_1..z_k];

    use R;
    monoR := (monomialIdeal(gens R))^d;
    Sd := flatten entries gens monoR;
    
    buffer := set Sd - candidate;
    bufferElems := toList buffer;

    -- Iterate through the buffer to check if a larger independent set exists 
    -- Store each subcandidate here
    --indepSet :=  set checkElements(bufferElems, toList candidate, d);

    subCandidates := {toList candidate};
    for i from 0 to (#bufferElems - 1) do (
	subCandidates = append(subCandidates, checkElements(bufferElems, toList candidate, d));
    );

    num := 0;
    for j from 1 to (#subCandidates - 1) do (
	if #subCandidates#j > #subCandidates#num then num = j;
    );

    indepSet := set subCandidates#num;

    return indepSet;
);


checkElements = (elementList, maxSet, d) -> (
    for i from 0 to (#elementList - 1) do (
	adjacent := isAdjacent(elementList#i, maxSet, d);
	if not adjacent then (
	    maxSet = checkElements(delete(elementList#i, elementList), append(maxSet, elementList#i), d);
	);
    );
    return maxSet;
);

isAdjacent = (e,s,d) -> (
    adjacent := false;

    for i from 0 to (#s - 1) do (
	m := lcm(e, s#i);
	degm := first degree m;
	if degm == d + 1 then (
	    adjacent = true;
	    break;
	);
    );

    return adjacent;
);


-- Takes a monomial and increases the indices of each indeterminate by one
--
-- Parameters:
--	i -> The monomial to be lifted
--	R -> The ring in which the lifted monomial will be placed

liftVars = (i,R) -> (
    use R;

    -- Produce a "Product" list for i
    factored = factor i;
    k := 1;

    -- Rebuild the monomial
    for j from 0 to (#factored - 1) do (
	k = k*x_(index(factored#j#0) + 2)^(factored#j#1);
    );
    return k;
);