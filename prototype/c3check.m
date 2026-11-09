/* c3check.m -- verify the first peeling step for the atoms with a negated point (item (6)
   of the Schur-polynomial remark rem:schur-atoms in the blueprint):
   (A) pair {t,-t} first: coefficient of t^(2g) in s_L(T u {-t_{j+1}}) equals
       (-1)^g * s_{L minus top two rows}(rest);
   (B) trio {t,t,-t} first: coefficient of t^(3g) (j>=2) resp. t^(3g-1) (j=1)
       equals (-1)^g * s_{L minus top three rows}(rest).
   Atoms computed as NA_j(+-t_i); the comparison Schur values via the e-minor
   dual JT for the reduced shape at the rest-alphabet. */
for g in [2..4] do
  P := PolynomialRing(Integers(), g);
  ts := [P.i : i in [1..g]];
  PS := PolynomialRing(P); z := PS.1;
  for j in [1..g] do
    T := ts cat ts[1..j]; Gj := g + j;
    Ez := &*[PS| 1 + t*z : t in T];
    ee := func<r | (r lt 0 or r gt Gj) select P!0 else Coefficient(Ez, r)>;
    M := Matrix(P, g, g, [[ee(Gj - (2*i - 1) + m) : m in [0..g-1]] : i in [1..g]]);
    rhs := [-ee(Gj - (2*i - 1) + g) : i in [1..g]];
    NAc := [P|];
    for m in [0..g-1] do
      Mm := M; for r in [1..g] do Mm[r][m+1] := rhs[r]; end for;
      Append(~NAc, Determinant(Mm));
    end for;
    Append(~NAc, Determinant(M));
    // helper: s_lambda(alphabet) for lambda' = (H, H-1, ..., H-h+1) shifted shapes is not
    // what we need; instead compute s of the REDUCED shape directly by its own dual JT:
    // reduced shape L' after removing top R rows of Lambda(j): L'_k = Lambda_{k+R}.
    // We only need its VALUE at the rest alphabet; use the h-JT (independent formula).
    lamfull := [g : c in [1..j+1]] cat [g - c : c in [1..g-1]];   // Lambda(j) as parts
    for CASE in ["A", "B"] do
      if CASE eq "A" then
        if j eq g then continue; end if;
        i0 := j + 1; R := 2; sgn := (-1)^g;
        atom := &+[P| NAc[m+1]*ts[i0]^m : m in [0..g]];   // NA(+t_{j+1}) ~ s(T u {-t_{j+1}})
        rest := [P| ]; for m in [1..g] do if m ne i0 then Append(~rest, ts[m]); end if; end for;
        rest cat:= [ts[m] : m in [1..j]];                  // T_j minus one t_{i0} copy... 
        // T_j = base + doubles(1..j); removing the +t_{j+1} single copy:
        rest := [ts[m] : m in [1..g] | m ne i0] cat [ts[m] : m in [1..j]];
      else
        i0 := j; R := 3; sgn := (-1)^g;
        atom := &+[P| NAc[m+1]*ts[i0]^m : m in [0..g]];   // NA(+t_j) ~ s(T u {-t_j})
        // alphabet T_j u {-t_j}: trio at t_j; rest = all slots except the three t_j's
        rest := [ts[m] : m in [1..g] | m ne i0] cat [ts[m] : m in [1..j] | m ne i0];
      end if;
      D := &+[Integers()| lamfull[k] : k in [1..R]];
      lamred := [lamfull[k] : k in [R+1..#lamfull]];
      // h-JT for s_{lamred}(rest)
      n := #lamred;
      cf := Coefficient(atom, i0, D);
      if n eq 0 then sval := P!1;
      else
        prec := (&+lamred) + n + 2;
        LS := LaurentSeriesRing(FieldOfFractions(P), prec);
        Hz := &*[LS| (1 - (LS!t)*LS.1)^-1 : t in rest];
        hh := func<r | r lt 0 select P!0 else P!Coefficient(Hz, r)>;
        Mh := Matrix(P, n, n, [[hh(lamred[a] - a + b) : b in [1..n]] : a in [1..n]]);
        sval := Determinant(Mh);
      end if;
      printf "g=%o j=%o case %o: deg-match %o, coeff = (-1)^g * s_red(rest): %o\n",
        g, j, CASE, Degree(atom, i0) eq D, (cf eq sgn*sval) or (cf eq -sgn*sval);
    end for;
  end for;
end for;
quit;
