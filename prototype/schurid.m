/* schurid.m -- verify detM_j = +- s_{lambda(j)}(T_j) with lambda(j)' = (G-1, ..., G-g),
   via the MONOMIAL expansion of the Schur function (independent of Jacobi-Trudi). */
for g in [2..4] do
  P := PolynomialRing(Integers(), g);
  ts := [P.i : i in [1..g]];
  PS := PolynomialRing(P); z := PS.1;
  SymS := SFASchur(Rationals()); SymM := SFAMonomial(Rationals());
  for j in [0..g] do
    T := ts cat ts[1..j]; Gj := g + j;
    Ez := &*[PS| 1 + t*z : t in T];
    ee := func<r | (r lt 0 or r gt Gj) select P!0 else Coefficient(Ez, r)>;
    M := Matrix(P, g, g, [[ee(Gj - k + m) : m in [0..g-1]] : k in [1..2*g-1 by 2]]);
    dM := Determinant(M);
    lamp := [Gj - i : i in [1..g]];
    lam := ConjugatePartition(lamp);
    mexp := SymM!(SymS.lam);
    Sn := SymmetricGroup(Gj);
    val := P!0;
    for mu in Support(mexp) do
      c := Coefficient(mexp, mu);
      if #Eltseq(mu) gt Gj then continue; end if;   // m_mu = 0 on Gj variables
      mup := Eltseq(mu) cat [0 : i in [#Eltseq(mu)+1..Gj]];
      vecs := {@ [mup[i^s] : i in [1..Gj]] : s in Sn @};
      val +:= (Integers()!c) * &+[P| &*[P| T[i]^v[i] : i in [1..Gj]] : v in vecs];
    end for;
    printf "g=%o j=%o lambda=%o : detM = +-s_lambda(T_j): %o\n",
      g, j, lam, (dM eq val) or (dM eq -val);
  end for;
end for;
quit;
