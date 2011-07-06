-- Macaulay2 function for computing an upper bound of the covering number
--
-- v1.1
-- Ben Babcock <bababcoc@lakeheadu.ca>
------------------------------------------------------------------------------

needsPackage "EdgeIdeals";

getMinimalCover = (n,d) -> (
	if n == 1 or d == 1 then return 1;
	if d == 2 then return n;

	k := binomial(d + n - 1, n - 1);
	S := QQ[x_1..x_n];
	T := QQ[z_1..z_k];

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
	W := flatten upCover;
	coveredVertices := unique apply(W, w -> inverseLegend#w);

	while true do (
		uncoveredVertices := toList(set(vertices G) - coveredVertices);
		if #uncoveredVertices == 0 then break;

		-- Select a random vertex and find the upward cliques associated with it
		v := legend#(uncoveredVertices#(random(0, #uncoveredVertices - 1)));
		U := select(values upwardCliques, i -> member(v, i));

		candidateClique := first U;
		for i from 1 when i < #U do (
			-- Determine how many vertices are in the cover
			vInCover := select(U#i, j -> member(j, W));
			if #vInCover == 0 or #vInCover < #select(candidateClique, j -> member(j, W)) then candidateClique = U#i;
		);

		-- Add the candidate clique to the cover
		upCover = append(upCover, candidateClique);
		coveredVertices = coveredVertices | apply(candidateClique, w -> inverseLegend#w);
	);

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

	return #upCover;
);