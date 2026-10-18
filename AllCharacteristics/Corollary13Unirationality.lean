import AllCharacteristics.KollarNormalizedUnirationality
import AllCharacteristics.KollarNormalizationGeometry
import AllCharacteristics.InternalCorayPaperConclusions

/-!
# Corollary 1.3: unirationality and degree-one zero-cycles

The normalized theorem constructs its parametrization internally.
No external unirationality input appears in these statements.

-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

open HomogeneousProjective

universe u

/-- A nonzero smooth cubic surface with a rational section is unirational
over its original field, without characteristic or cardinality restrictions. -/
theorem smoothCubic_unirational_of_rational_section
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (s : Spec (.of k) ⟶ hypersurface F hF)
    (hs : s ≫ hypersurfaceToBase F hF = 𝟙 _) :
    IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF) := by
  apply isUnirationalOver_of_normalized_cubic_theorem ?_ F hF hF0 s hs
  intro G hG hSmooth c hc hp hd
  subst G
  exact isUnirationalOver_normalized_smooth_cubic c hG hp hd

/-- Corollary 1.3 of the manuscript: a smooth cubic surface is unirational
if and only if it admits a zero-cycle of degree one. The rational-section
step uses the internally proved Cassels–Swinnerton-Dyer theorem. -/
theorem twoProofs_corollary13_unirational_iff_zeroCycle_degree_one
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)] :
    IsUnirationalOver k (hypersurface F hF) (hypersurfaceToBase F hF) ↔
      ∃ z : ZeroCycle (hypersurface F hF),
        ZeroCycle.degree (hypersurfaceToBase F hF) z = 1 := by
  constructor
  · exact zeroCycle_degree_one_of_unirational_smoothCubic F hF
  · intro hz
    obtain ⟨s, hs⟩ := (twoProofs_main_theorem_internalCoray001 F hF).mpr hz
    exact smoothCubic_unirational_of_rational_section F hF hF0 s hs

end AllCharacteristics
