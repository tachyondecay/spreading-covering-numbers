-- 
-- v0.3
-- Ben Babcock <bababcoc@lakeheadu.ca>
--


-- Determine whether an orbit is a clique
isClique = method();
isClique(List) := (orbit) -> (
	for i to (#orbit - 2) do (
		if (orbit#i - orbit#(i + 1) > 1) then return false
	);
	return true;
);


-- Determine whether an orbit is an independent set
isIndependent = method();
isIndependent(List) := (orbit) -> (
	for i to (#orbit - 2) do (
		if (orbit#i - orbit#(i + 1)) == 1 then return false;
	);
	return true;
);

-- List all the orbits of S_n(d)
-- These correspond to the partitions of d of length at most n
orbits = method();
orbits(ZZ,ZZ) := (n,d) -> (
	-- We want partitions of d
	parts := partitions d;

	-- Now keep only those partitions of length n or smaller
	parts = select(parts, i -> (#i <= n));

	-- A plain list is fine, and we want to pad shorter entries
	return apply(parts, i -> (
			i = toList i;
			if #i < n then (
				difference := n - #i;
				zeros := for j from 1 to difference list 0;
				return (i | zeros);
			) else return i;
		));
);


-- Check if two orbits are adjacent (i.e., every vertex in orbit1 is adjacent 
-- to a vertex in orbit2).
orbitsAdjacent = method();
orbitsAdjacent(List,List) := (orbit1,orbit2) -> (
	-- Orbits must be same length
	if #orbit1 != #orbit2 then error "Expected orbits of same length.";

	differences := for i to (#orbit1 - 1) list orbit1#i - orbit2#i;
	if ((#positions(differences, i -> (i == 1)) == 1) and 
		#positions(differences, i -> (i == -1)) == 1) then return true
	else return false;
);


-- Calculate how many vertices are in the orbit
orbitalSize = method();
orbitalSize(List) := (orbit) -> (
	-- For each unique entry in the orbit, compute its multiplicity
	repetitions := product apply(unique orbit, 
		entry -> ((#positions(orbit, i -> (i == entry)))!));

	return (((#orbit)!)/repetitions);
);

orbitalSpread = method();
orbitalSpread(ZZ,ZZ) := (n,d) -> (
	--R := QQ[x_1..x_n];
	allOrbits := orbits(n,d);
	spreadingNum := n;

	takenOrbits := take(allOrbits, 1);
	allOrbits = drop(allOrbits, 2);
	for i to (#allOrbits - 1) do (
		currentOrbit := allOrbits#i;
		if not any(takenOrbits, i -> (orbitsAdjacent(i,currentOrbit))) then (
			if isIndependent(currentOrbit) then spreadingNum = spreadingNum + orbitalSize(currentOrbit)
			else if isClique(currentOrbit) then spreadingNum = spreadingNum + 1
			else spreadingNum = spreadingNum + n;
			takenOrbits = append(takenOrbits, currentOrbit);
		);
	);

	return spreadingNum;
);