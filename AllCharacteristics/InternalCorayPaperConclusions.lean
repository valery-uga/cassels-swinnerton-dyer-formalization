import PfaffianDescent.CorayOriginalDegreeOneCycleInternalClosure
import AllCharacteristics.TwoProofs
import AllCharacteristics.TwoProofsLiteralFiniteExtension
import AllCharacteristics.TwoProofsLiteralChaptersFiveSix

/-! Public paper conclusions with the internally proved Coray construction.
Original fields, cubic equations, maps and degree statements are retained.
No external Coray/Voisin theorem or geometric outcome is an input. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open HomogeneousProjective
universe u
set_option autoImplicit false

/-- The actual original characteristic-zero Coray proof, uniformly in the
field used by the existing characteristic-zero lifting/reduction route. -/
theorem internalCorayDegreeOneFourOrTenFor_uniform001 :
    ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K := by
  intro K hField hCharZero
  exact PfaffianDescent.Coray.internalCorayDegreeOneFourOrTenFor_charZero001 (K := K)

/-- The original paper endpoint with its uniform Coray premise supplied
by the actual internal proof; all remaining original hypotheses retained. -/
theorem twoProofs_main_theorem_internalCoray001
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
    (∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  twoProofs_main_theorem internalCorayDegreeOneFourOrTenFor_uniform001 p hp

/-- The original paper endpoint with its uniform Coray premise supplied
by the actual internal proof; all remaining original hypotheses retained. -/
theorem twoProofs_finite_point_coprime_has_point_internalCoray001
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  twoProofs_finite_point_coprime_has_point internalCorayDegreeOneFourOrTenFor_uniform001 p hp hdegree x hx heval

/-- The original paper endpoint with its uniform Coray premise supplied
by the actual internal proof; all remaining original hypotheses retained. -/
theorem twoProofs_intro_finiteExtension_iff_internalCoray001
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ↔
    (∃ (L : Type u) (hL : Field L),
      letI := hL
      ∃ hAlg : Algebra k L,
        letI := hAlg
        ∃ _ : Module.Finite k L,
          Nat.Coprime (Module.finrank k L) 3 ∧
          ∃ x : Fin 4 → L, x ≠ 0 ∧ p.eval₂ (algebraMap k L) x = 0) :=
  twoProofs_intro_finiteExtension_iff_of_coray internalCorayDegreeOneFourOrTenFor_uniform001 p hp

/-- The original paper endpoint with its uniform Coray premise supplied
by the actual internal proof; all remaining original hypotheses retained. -/
theorem twoProofs_chapterFive_charzero_internalCoray001
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_charzero internalCorayDegreeOneFourOrTenFor_uniform001 p hp z hz

/-- The original paper endpoint with its uniform Coray premise supplied
by the actual internal proof; all remaining original hypotheses retained. -/
theorem twoProofs_chapterFive_smooth_internalCoray001
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth internalCorayDegreeOneFourOrTenFor_uniform001 p hp z hz

/-- The original paper endpoint with its uniform Coray premise supplied
by the actual internal proof; all remaining original hypotheses retained. -/
theorem twoProofs_chapterSix_main_internalCoray001
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    ((∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ∧
    ((∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
      ∃ z : ZeroCycle (hypersurface p hp),
        ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  twoProofs_chapterSix_main internalCorayDegreeOneFourOrTenFor_uniform001 p hp

end AllCharacteristics
end
