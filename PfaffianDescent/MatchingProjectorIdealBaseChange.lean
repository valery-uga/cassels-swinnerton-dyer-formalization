import PfaffianDescent.PolynomialLinearChange
import PfaffianDescent.BasisMatchingProjectorInvariance

/-! SOURCE ONLY, UNVERIFIED. Literal homogeneous linear-equation ideal,
with scalar extension equality on the IDEAL, retaining nilpotents. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectorLineIdeal (P : Matrix (Fin 4) (Fin 4) K) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  ⟨Ideal.span (Set.range (linearCoordinate (1 - P))), by
    apply Ideal.homogeneous_span
    rintro q ⟨m, rfl⟩
    exact ⟨1, linearCoordinate_homogeneous (1 - P) m⟩⟩

theorem projectorLineIdeal_baseChange {E : Type u} [Field E]
    (f : E →+* K) (P : Matrix (Fin 4) (Fin 4) E) :
    (projectorLineIdeal P).toIdeal.map (MvPolynomial.map f) =
      (projectorLineIdeal (P.map f)).toIdeal := by
  classical
  change (Ideal.span (Set.range (linearCoordinate (1 - P)))).map
      (MvPolynomial.map f) =
    Ideal.span (Set.range (linearCoordinate (1 - P.map f)))
  rw [Ideal.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨r, ⟨m, rfl⟩, rfl⟩
    refine ⟨m, ?_⟩
    rw [linearCoordinate_map]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  · rintro ⟨m, rfl⟩
    refine ⟨linearCoordinate (1 - P) m, ⟨m, rfl⟩, ?_⟩
    rw [linearCoordinate_map]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp

end PfaffianDescent.QuarticNet
