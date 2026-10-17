import PfaffianDescent.QuarticMatchingLines
import PfaffianDescent.HomogeneousQuotientMap

/-! SOURCE ONLY, UNVERIFIED. The polynomial restriction conclusions yield
actual closed projective line immersions into the SAME cubic, with exact
ambient squares. The line ideals are the actual two coordinate linear equations. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateMatchingLineIdeal (side : Bool) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  if side then
    ⟨Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) K)), by
      apply Ideal.homogeneous_span
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> exact ⟨1, isHomogeneous_X K _⟩⟩
  else
    ⟨Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) K)), by
      apply Ideal.homogeneous_span
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> exact ⟨1, isHomogeneous_X K _⟩⟩

def coordinateMatchingLineRestriction (side : Bool) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K :=
  if side then coordinateLineRestriction23 else coordinateLineRestriction

theorem coordinateMatchingLineRestriction_zero_iff_mem
    (side : Bool) (F : MvPolynomial (Fin 4) K) :
    coordinateMatchingLineRestriction side F = 0 ↔
      F ∈ (coordinateMatchingLineIdeal (K := K) side).toIdeal := by
  let J := (coordinateMatchingLineIdeal (K := K) side).toIdeal
  let mk := Ideal.Quotient.mkₐ K J
  let back : MvPolynomial (Fin 2) K →ₐ[K] (MvPolynomial (Fin 4) K ⧸ J) :=
    if side then aeval ![mk (X 2), mk (X 3)] else aeval ![mk (X 0), mk (X 1)]
  have hcomp : back.comp (coordinateMatchingLineRestriction side) = mk := by
    have hkill (m : Fin 4) (hm : X m ∈ J) : mk (X m) = 0 := by
      change Ideal.Quotient.mk J (X m) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    cases side
    · have h2 : mk (X 2) = 0 := by
        apply hkill
        change X 2 ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) K))
        exact Ideal.subset_span (by simp)
      have h3 : mk (X 3) = 0 := by
        apply hkill
        change X 3 ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) K))
        exact Ideal.subset_span (by simp)
      ext m : 1
      fin_cases m <;> simp [back, coordinateMatchingLineRestriction,
        coordinateLineRestriction, AlgHom.comp_apply, h2, h3]
    · have h0 : mk (X 0) = 0 := by
        apply hkill
        change X 0 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) K))
        exact Ideal.subset_span (by simp)
      have h1 : mk (X 1) = 0 := by
        apply hkill
        change X 1 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) K))
        exact Ideal.subset_span (by simp)
      ext m : 1
      fin_cases m <;> simp [back, coordinateMatchingLineRestriction,
        coordinateLineRestriction23, AlgHom.comp_apply, h0, h1]
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change mk F = 0
    rw [← AlgHom.congr_fun hcomp F, AlgHom.comp_apply, h, map_zero]
  · intro h
    have hker : J ≤ RingHom.ker (coordinateMatchingLineRestriction side).toRingHom := by
      cases side <;> dsimp only [J, coordinateMatchingLineIdeal, ↓reduceIte] <;>
        apply Ideal.span_le.mpr <;> intro p hp <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp <;>
        rcases hp with rfl | rfl <;>
        simp [coordinateMatchingLineRestriction, coordinateLineRestriction,
          coordinateLineRestriction23]
    exact hker h

theorem equationIdeal_le_coordinateMatchingLineIdeal
    (side : Bool) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hline : coordinateMatchingLineRestriction side F = 0) :
    (equationIdeal F hF).toIdeal ≤ (coordinateMatchingLineIdeal (K := K) side).toIdeal := by
  apply Ideal.span_le.mpr
  intro q hq
  have hqF : q = F := Set.mem_singleton_iff.mp hq
  rw [hqF]
  exact (coordinateMatchingLineRestriction_zero_iff_mem side F).mp hline

def coordinateMatchingLineToCubic
    (side : Bool) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hline : coordinateMatchingLineRestriction side F = 0) :
    scheme (coordinateMatchingLineIdeal (K := K) side) ⟶ hypersurface F hF :=
  schemeQuotientMap (equationIdeal F hF) (coordinateMatchingLineIdeal side)
    (equationIdeal_le_coordinateMatchingLineIdeal side F hF hline)

instance coordinateMatchingLineToCubic_isClosedImmersion
    (side : Bool) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hline : coordinateMatchingLineRestriction side F = 0) :
    IsClosedImmersion (coordinateMatchingLineToCubic side F hF hline) :=
  schemeQuotientMap_closedImmersion _ _ _

@[reassoc] theorem coordinateMatchingLineToCubic_toAmbient
    (side : Bool) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hline : coordinateMatchingLineRestriction side F = 0) :
    coordinateMatchingLineToCubic side F hF hline ≫ quotientProjMap (equationIdeal F hF) =
      quotientProjMap (coordinateMatchingLineIdeal (K := K) side) :=
  schemeQuotientMap_comp_quotientProjMap _ _ _

end PfaffianDescent.QuarticNet
