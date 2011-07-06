-- Macaulay2 function for recursively finding the spreading number
--
-- Ben Babcock <bababcoc@lakeheadu.ca>
-------------------------------------------------------------------------------

saveSpreadCache = method();

saveSpreadCache(MutableHashTable) := (cache) -> (
    out := new MutableHashTable;

    -- Iterate through the keys
    k := keys cache;
    for i from 0 to (#k - 1) do (
	out#(k#i) = new MutableHashTable;

	v := keys cache#(k#i);
	for j from 0 to (#v - 1) do (
	    out#(k#i)#(v#j) = toExternalString cache#(k#i)#(v#j);
	);
    );

    return out;
);

saveSpreadCache(String, MutableHashTable) := (filename, cache) -> (
    fn = openOut filename;
    
    outputCache := saveSpreadCache(cache);
    out := "new MutableHashTable from {";

    k := keys outputCache;
    for i from 0 to (#k - 1) do (
	out = out || "	" | k#i | " => new MutableHashTable from {";

	v := keys outputCache#(k#i);
	for j from 0 to (#v - 1) do (
	    out = out || "		" | v#j | " => " | outputCache#(k#i)#(v#j) | ",";
	);

	out = out || "	" | "}, ";
    );
    out = out || "}";

    fn << out;
    close fn;
);

spreadNumber = method();

spreadNumber(ZZ,ZZ) := (n,d) -> spreadNumber(n,d,new MutableHashTable);

spreadNumber(ZZ,ZZ,MutableHashTable) := (n,d,cache) -> (
    if not (cache#?n and cache#n#?d) then (
	cache = spreadSeries(n,d,cache);
    );
    return first degree denominator cache#n#d;
);

spreadSeries = method();

spreadSeries(ZZ,ZZ) := (n,d) -> spreadSeries(n,d,new MutableHashTable);

spreadSeries(ZZ,ZZ,MutableHashTable) := (n,d,cache) -> (
    << "Series for n = " << n << ", d = " << d << endl;
    x := local x;
    z := local z;

    -- Check if the Hilbert Series is present in the cache
    if cache#?n then (
	if cache#n#?d then (
	    return cache;
	);
    );

    if n == 1 then (
	if not cache#?1 then cache#1 = new MutableHashTable;
	cache#1#d = hilbertSeries(QQ[x]);
	return cache;
    );

    k := binomial(n + d - 1, n - 1);
    t := binomial(n + d - 2, n - 2);

    S := QQ[x_1..x_n];
    T := QQ[z_1..z_k];

    use S;

    -- Find the generators of the Stanley-Reinser ideal

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

    -- Construct the Stanley-Reisner ideal
    use T;
    L := {0_T};	-- Necessary if n = 1
    for i from 0 to (#Pairs - 1) do (
	L = append(L,(Pairs#i#0)*(Pairs#i#1));
    );

    << "Computing Stanley-Reisner ideal." << endl;
    time I := monomialIdeal(L);

    if d == 1 then return hilbertSeries(I, Reduce=>true);

    << "Computing intersection." << endl;
    time J := intersect(I, monomialIdeal(z_(t + 1)..z_k));

    << "Computing polynomial ring HS." << endl;
    time zRingHS := hilbertSeries(QQ[z_1..z_t]);

    << "Computing intersection HS." << endl;
    time JHS := hilbertSeries(J, Reduce => true);

    A := degreesRing T;
    T := A_0;
    Z := frac ZZ[T];

    << "Computing previous HS." << endl;
    time prevHS := spreadSeries(n - 1, d);
    prevHS = prevHS#(n - 1)#d;
    
    zRingHS = sub(zRingHS,frac Z);
    JHS = sub(JHS,frac Z);
    prevHS = sub(prevHS,frac Z);

    denoms := {value denominator prevHS, value denominator JHS, value denominator zRingHS};
    cnum := (numerator prevHS) * denoms#1 * denoms#2 + 
		(numerator JHS) * denoms#0 * denoms#2 - 
		(numerator zRingHS * denoms#0 * denoms#1);

    denom := sub(denoms#0 * denoms#1 * denoms#2, Z);
    cnum = sub(cnum, Z);

    << endl << endl;

    if not cache#?n then cache#n = new MutableHashTable;
    cache#n#d = (cnum/denom);
    return cache;
);