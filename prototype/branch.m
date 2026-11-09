/* branch.m -- NA_j(z) as a single Schur polynomial of the extended alphabet:
   check  sum_m NA_m z^m = +- s_{lambda(j)'=(G..G-g+1)}(T_j u {eps z}) for eps = +-1,
   via the e-minor with the extra factor (1 + eps*z*w) in the generating poly. */
for g in [2..3] do
  P := PolynomialRing(Integers(), g + 1);      // t1..tg and w
  ts := [P.i : i in [1..g]]; w := P.(g+1);
  PS := PolynomialRing(P); z := PS.1;
  for j in [0..g] do
    T := ts cat ts[1..j]; Gj := g + j;
    for eps in [1, -1] do
      Ez := &*[PS| 1 + t*z : t in T] * (1 + eps*w*z);   // alphabet + {eps w}
      ee := func<r | (r lt 0 or r gt Gj + 1) select P!0 else Coefficient(Ez, r)>;
      // the g x g moment determinant of the EXTENDED alphabet, size still g:
      // rows k odd (g rows), cols m = 0..g-1, G -> Gj + 1
      Me := Matrix(P, g, g, [[ee(Gj - (2*i - 1) + m) : m in [1..g]] : i in [1..g]]);
      dext := Determinant(Me);
      // NA(z) of the UNEXTENDED system, evaluated at eps*w... compare:
      Ez0 := &*[PS| 1 + t*z : t in T];
      e0 := func<r | (r lt 0 or r gt Gj) select P!0 else Coefficient(Ez0, r)>;
      M0 := Matrix(P, g, g, [[e0(Gj - (2*i - 1) + m) : m in [0..g-1]] : i in [1..g]]);
      rhs := [-e0(Gj - (2*i - 1) + g) : i in [1..g]];
      NAc := [P|];
      for m in [0..g-1] do
        Mm := M0; for r in [1..g] do Mm[r][m+1] := rhs[r]; end for;
        Append(~NAc, Determinant(Mm));
      end for;
      Append(~NAc, Determinant(M0));
      NAval := &+[P| NAc[m+1]*(-eps*w)^m : m in [0..g]];   // crossed: s(T u {eps w}) ~ NA(-eps w)
      printf "g=%o j=%o eps=%o : detM(T u {eps w}) = +- NA(eps w): %o\n",
        g, j, eps, (dext eq NAval) or (dext eq -NAval);
    end for;
  end for;
end for;
quit;
