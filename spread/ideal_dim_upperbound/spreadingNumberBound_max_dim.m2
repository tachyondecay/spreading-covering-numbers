-- Macaulay2 algorithm for finding an upper bound for the spreading number
-- 
-- Ben Babcock <bababcoc@lakeheadu.ca>
------------------------------------------------------------------------------

needsPackage "EdgeIdeals";
spreadingNumberBound = (n,d) -> (
	if n == 1 or d == 1 then return 1;
	if d == 2 then return n;

	k := binomial(d + n - 1, n - 1);
	x := local x;
	z := local z;

	S := QQ[x_1..x_n];
	T := QQ[z_1..z_k];

	-- In the ring S, first determine all monomials of degree D. Second,
	-- determine which pair of monomials have a LCM of degree D+1

	monoS := (monomialIdeal(gens S))^d;
	Sd := flatten entries gens monoS;
	Pairs := {};
	for i from 1 to k do (
		for j from (i + 1) to k do (
			m := lcm(Sd#(i - 1), Sd#(j - 1));
			degm := first degree m;
			if degm == d + 1 then Pairs = append(Pairs,{z_i, z_j});
		);
	);

	G := graph(T,Pairs);
	L := vertices G;
	W := {};

	while(#L > 0) do (
		v := first L;
		if #W == 0 then v = L#(random(0, #L - 1))
		else (
			-- Select a vertex of minimum degree
			dV := apply(L, i -> degreeVertex(G, i));
			v = L#(position(dV, i -> i == min dV));
		);

		-- Add that vertex to the set
		W = append(W,v);

		-- Remove v and its neighbours from L
		L = toList(set(L) - ({v} | neighbors(G,v)));
	);

	-- For each vertex in the maximal set, find its neighbours and add them to that vertex
	newGens := apply(W, v -> (v + sum neighbors(G,v)));
	edgeIdealGens := apply(edges G, product);

	-- Create a new ideal with these new generators
	modifiedIdeal := ideal(newGens | edgeIdealGens);
	modifiedIdealDim := time dim(T/modifiedIdeal);
	upperBound := modifiedIdealDim + #newGens;

	-- If the upper bound matches the cardinality of the maximal set, then it must be 
	-- the spreading number.
	if #W == upperBound then print "Lower bound and upper bound equal.";
	return upperBound;
);

