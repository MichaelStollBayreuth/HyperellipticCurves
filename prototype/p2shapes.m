/* p2shapes.m -- identify all Cramer objects as skew Schur functions:
   NA_m(j) = +- s_{lambda/(m)}(T_j), lambda' = (G, G-1, ..., G-g+1), via the
   INDEPENDENT h-Jacobi-Trudi determinant (m = g gives detM). */
for g in [2..3] do
  P := PolynomialRing(Integers(), g);
  ts := [P.i : i in [1..g]];
  PS := PolynomialRing(P); z := PS.1;
  for j in [0..g] do
    T := ts cat ts[1..j]; Gj := g + j;
    Ez := &*[PS| 1 + t*z : t in T];
    ee := func<r | (r lt 0 or r gt Gj) select P!0 else Coefficient(Ez, r)>;
    prec := 3*Gj + 2*g + 4;
    LS := LaurentSeriesRing(FieldOfFractions(P), prec);
    Hz := &*[LS| (1 - (LS!t)*LS.1)^-1 : t in T];
    hh := func<r | r lt 0 select P!0 else P!Coefficient(Hz, r)>;
    lamp := [Gj - i + 1 : i in [1..g]];
    lam := ConjugatePartition(lamp);
    n := #lam;
    for m in [0..g] do
      cols := [c : c in [0..g] | c ne m];
      Me := Matrix(P, g, g, [[ee((Gj - 2*i + 1) + cols[s]) : s in [1..g]] : i in [1..g]]);
      de := Determinant(Me);
      mu := [m] cat [0 : i in [2..n]];
      Mh := Matrix(P, n, n, [[hh(lam[i] - mu[s] - i + s) : s in [1..n]] : i in [1..n]]);
      dh := Determinant(Mh);
      printf "g=%o j=%o m=%o : e-minor = +-s_{lambda/(%o)}: %o\n",
        g, j, m, m, (de eq dh) or (de eq -dh);
    end for;
  end for;
end for;
quit;
