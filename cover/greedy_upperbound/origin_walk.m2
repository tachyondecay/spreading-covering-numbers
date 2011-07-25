needsPackage "EdgeIdeals";

coveringNumberBound = (n,d) -> (
	<< "Degree " << d << " in " << n << " variables " << endl;
	if n == 1 or d == 1 then return 1;
	if d == 2 then return n;

	k := binomial(d + n - 1, n - 1);
	S := QQ[x_1..x_n];
	T := QQ[z_1..z_k];

	sGroup := symmetricGroup S;

	-- In the ring S, first determine all monomials of degree d. Second,
	-- determine which pair of monomials have a LCM of degree d + 1
	Sd := flatten entries gens((monomialIdeal(gens S))^d);
	Pairs := {};
	legend := {};
	for i from 1 to k do (
		legend = append(legend, {z_i, Sd#(i - 1)});
		for j from (i + 1) to k do (
			m := lcm(Sd#(i - 1), Sd#(j-1));
			degm := first degree m;
			if degm == d + 1 then Pairs = append(Pairs,{z_i,z_j});
		);
	);


	-- This table will match up generators of T with monomials of S_n(d)
	legend = hashTable legend;
	inverseLegend := applyPairs(legend, (p,q) -> (q,p));

	-- Construct the graph S_n(d)
	G := graph(T, Pairs);

	-- Find all upward cliques (each is identified by a monomial from S_n(d - 1))
	SdMinus1 := flatten entries gens((monomialIdeal(gens S))^(d - 1));
	upwardCliques := hashTable apply(SdMinus1, i -> ({i, for j from 1 to n list i*x_j}));

	-- Our initial set, for the cover generator, will be the cliques containing 
	-- x_1^d,...,x_n^d, because these each belong to one and only one clique.
	upCover := for i from 1 to n list upwardCliques#(x_i^(d - 1));

	-- Get a list of all vertices in the cover
	W := unique flatten upCover;

	graphOrbits := reverse orbits(n,d);
	for orb when orb < #graphOrbits do (
		--<< "Orbit: " << graphOrbits#orb << endl;
		f := factor product for i when i < #(graphOrbits#orb) list x_(i+1)^(graphOrbits#orb#i);
		for i when i < #sGroup do (
			sigma := sGroup#i;
			v := product for j when j < #f list (x_(sigma#(index(f#j#0)) + 1)^(f#j#1));

			-- If v is in the cover, skip it
			if member(v, W) then continue;
		
			-- Find the upward cliques that contain v
			U := select(values upwardCliques, i -> member(v, i));

			candidateClique := first U;
			for i from 1 when i < #U do (
				-- Determine how many vertices are in the cover
				vInCover := select(U#i, j -> member(j, W));
				if #vInCover == 0 or #vInCover < #select(candidateClique, j -> member(j, W)) then candidateClique = U#i;
			);

			-- Add the candidate clique to the cover
			upCover = append(upCover, candidateClique);
			W = W | candidateClique;
		);
	);

	print ("Unminimized cover (size: " | #upCover | ")");
	--print upCover;

	-- Minimize the cover
	while true do (
		-- Get the frequency for each vertex (how many cliques contain it)
		vertexFreq := new MutableHashTable;
		for i when i < #upCover do (
			for j when j < #(upCover#i) do (
				v := (upCover#i)#j;
				if vertexFreq#?v then vertexFreq#v = vertexFreq#v + 1
				else vertexFreq#v = 1;
			);
		);

		-- Iterate over the cliques. If there is a clique in which no vertex is of frequency
		-- 1, then the clique is not essential to the cover and may be discarded
		discard := for i when i < #upCover do (
			c := upCover#i;
			essential := false;
			for j when j < #c do (
			if vertexFreq#(c#j) == 1 then (essential = true; break;);
			);
			if not essential then break i;
		);

		if discard =!= null then upCover = drop(upCover, {discard,discard})
		else break;
	);

	print("Minimized cover (size " | #upCover | ")");
	--print upCover;

	return #upCover;
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


-- Return a list of elements of the symmetric group of degree n
symmetricGroup = method();
symmetricGroup(Ring) := R -> (
	-- This line from the Monomial Ideals chapter, by Serkan Hosten and Gregory Smith, 
	-- of Computations in Algebraic Geometry with Macaulay2
	L := terms det matrix table(numgens R, gens R, (i,r) -> r^(i + 1));
	sGroup := {};

	-- Construct a hashtable to represent each permutation (starting from 0 instead of 1)
	for i from 0 to (#L - 1) do (
		elem := {};
		f := factor L#i;
		for j from 0 to (#f - 1) do (
			if index f#j#0 =!= null then elem = append(elem, {index f#j#0, f#j#1 - 1});
		);
		sGroup = append(sGroup, hashTable elem);
	);

	return sGroup;
);