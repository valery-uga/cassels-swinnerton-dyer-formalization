import Mathlib.RingTheory.Artinian.Module

namespace PfaffianDescent

/-- A prime ideal containing an ideal with Artinian quotient is maximal. -/
theorem ideal_isMaximal_of_isArtinian_quotient
    {R : Type*} [CommRing R] (I P : Ideal R)
    [IsArtinianRing (R ⧸ I)] [P.IsPrime] (hIP : I ≤ P) : P.IsMaximal := by
  let Q : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) P
  have hQprime : Q.IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIP
  have hQmax : Q.IsMaximal := IsArtinianRing.isMaximal_of_isPrime Q
  have hPQ : Q.comap (Ideal.Quotient.mk I) = P :=
    Ideal.comap_map_mk hIP
  rw [← hPQ]
  exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

end PfaffianDescent
