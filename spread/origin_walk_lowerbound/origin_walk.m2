--
--
--

needsPackage "EdgeIdeals";


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


-- This is the main event.
-- Required Parameters
--	n 	The number of indeterminates, x_1..x_n
--	d	The degree of the monomials that interest us
-- Options
--	OutputSet	Boolean. When true, output the maximum independent 
--			set.  When false, output just the number.  Default false.
spreadingNumberBound = method(Options => {OutputSet => false});

spreadingNumberBound(ZZ,ZZ) := opts -> (n,d) -> (
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

	-- If n divides d, then there is a single, central vertex.
	-- Otherwise, compute the central clique and take a vertex from there.
	origin := null;
	if n % d == 0 then origin = inverseLegend#(product(for i from 1 to n list x_i^(n//d)))
	else (
		centralOrbit := last orbits(n,d);
		origin = inverseLegend#(product(for i from 1 to n list x_i^(centralOrbit#(i - 1))));
	);

	-- We will keep a running list of all the vertices we might be able to take
	eligibleVertices := delete(origin, vertices G);
	finalSet := {origin};
	previousOrigin := origin;

	backTracking := false;
	originList := {origin};
	while(true) do (
		--<< "eligible vertices: " << eligibleVertices << endl;
		--<< "origin: " << legend#origin << endl << endl;
		if #eligibleVertices == 0 then break;

		-- Get all the neighbours of our origin vertex
		hexagon := neighbors(G,origin);
		candidates := select(neighbors(G,hexagon), i -> (member(i, eligibleVertices)));
		eligibleVertices = toList(set(eligibleVertices) - set(hexagon));

		-- If we don't find any candidates, backtrack to previous origin.
		if #candidates == 0 then (
			originList = drop(originList,-1);
			origin = last originList;
		)
		else (
			origin = first candidates;
			maxhexdegree := 0;
			for i from 0 to (#candidates - 1) do (
				hexdegree := #select(neighbors(G,candidates#i), j -> member(j, hexagon));
				if hexdegree > maxhexdegree then (
					--<< "Found " << hexdegree << " adjacent." << endl;
					origin = candidates#i;
					maxhexdegree = hexdegree;
				)
			);
			--print "Break";
			finalSet = append(finalSet,origin);
			eligibleVertices = delete(origin, eligibleVertices);
			originList = append(originList,origin);
		);
		collectGarbage();
	);

	if opts.OutputSet then return apply(finalSet, v -> legend#v)
	else return #finalSet;
);