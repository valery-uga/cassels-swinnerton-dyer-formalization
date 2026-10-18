import PfaffianDescent.HilbertBurchCofactorLift318
import PfaffianDescent.LiftedSyzygyFiniteFlat318

/-!
Construct a determinantal finite-flat lift from a downstairs Hilbert--Burch
presentation. Generation of the downstairs ideal and exactness of its
relations are explicit hypotheses of this algebraic consumer. The surface
Hilbert--Burch constructions supply those hypotheses for arbitrary
finite-flat surface ideals. No upstairs matrix, ideal, flatness,
finiteness, or rank outcome is an input.
-/

noncomputable section
namespace PfaffianDescent
open Module Matrix
open scoped BigOperators
universe u v w t

/-- Cofactor ideal transport follows from the actual generator reductions;
it does not require surjectivity of the ring map. -/
lemma hilbertBurchCofactorIdeal_map318
    {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : A' →+* A) (N : Matrix (Option ι) ι A') :
    (Ideal.span (Set.range (hilbertBurchCofactors318 N))).map π =
      Ideal.span (Set.range (hilbertBurchCofactors318 (N.map π))) := by
  have hfun : (fun i => π (hilbertBurchCofactors318 N i)) =
      hilbertBurchCofactors318 (N.map π) :=
    funext (hilbertBurchCofactors_map318 π N)
  rw [Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f : Option ι → A => Ideal.span (Set.range f)) hfun

/-- A downstairs finite-flat quotient with its actual rectangular
Hilbert--Burch presentation lifts as a whole finite-free-flat quotient
across a square-zero coefficient extension, with the same original rank.
All lifted generators and all lifted relations are constructed. -/
theorem exists_hilbertBurch_prescribedFiniteFlat_lift318
    {R : Type u} {S : Type v} {A' : Type w} {A : Type t}
    [CommRing R] [CommRing S] [IsLocalRing S] [CommRing A'] [CommRing A]
    [Algebra R S] [Algebra R A'] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Flat R A']
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (π : A' →ₐ[R] A) (hπ : Function.Surjective π)
    (hK : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap R S)).map (algebraMap R A'))
    (M : Matrix (Option ι) ι A) (J : Ideal A)
    (hJ : J = Ideal.span (Set.range (hilbertBurchCofactors318 M)))
    (hrelations : ∀ a : Option ι → A,
      (∑ i, a i * hilbertBurchCofactors318 M i) = 0 →
      ∃ b : ι → A, ∀ i, a i = ∑ j, M i j * b j)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)] :
    ∃ (N : Matrix (Option ι) ι A') (J' : Ideal A'),
      N.map π.toRingHom = M ∧
      J' = Ideal.span (Set.range (hilbertBurchCofactors318 N)) ∧
      J'.map π.toRingHom = J ∧
      (∀ i, π (hilbertBurchCofactors318 N i) = hilbertBurchCofactors318 M i) ∧
      Module.Finite R (A' ⧸ J') ∧
      Module.Free R (A' ⧸ J') ∧
      Module.Flat R (A' ⧸ J') ∧
      Module.finrank R (A' ⧸ J') = Module.finrank S (A ⧸ J) := by
  obtain ⟨N, hmap, hcof, hsyz⟩ :=
    exists_hilbertBurch_matrix_lift318 π.toRingHom hπ M
  let J' := Ideal.span (Set.range (hilbertBurchCofactors318 N))
  have hmapJ : J'.map π.toRingHom = J := by
    change (Ideal.span (Set.range (hilbertBurchCofactors318 N))).map π.toRingHom = J
    rw [hilbertBurchCofactorIdeal_map318, hmap, ← hJ]
  have hrelationsN : ∀ a : Option ι → A,
      (∑ i, a i * π (hilbertBurchCofactors318 N i)) = 0 →
      ∃ b : ι → A, ∀ i, a i = ∑ j, π (N i j) * b j := by
    intro a ha
    have haM : (∑ i, a i * hilbertBurchCofactors318 M i) = 0 := by
      have hcof' : ∀ i, π (hilbertBurchCofactors318 N i) =
          hilbertBurchCofactors318 M i := hcof
      simpa only [hcof'] using ha
    obtain ⟨b, hb⟩ := hrelations a haM
    refine ⟨b, ?_⟩
    intro i
    rw [hb i]
    apply Finset.sum_congr rfl
    intro j hj
    have hij := congrArg (fun T : Matrix (Option ι) ι A => T i j) hmap
    change π (N i j) = M i j at hij
    rw [hij]
  obtain ⟨hfinite, hfree, hflat, hrank⟩ :=
    AllCharacteristics.liftedSyzygy_prescribedFiniteFlat_local318
      hRS hI π hπ hK (hilbertBurchCofactors318 N) N J hmapJ.symm hsyz hrelationsN
  exact ⟨N, J', hmap, rfl, hmapJ, hcof, hfinite, hfree, hflat, hrank⟩

end PfaffianDescent
end
