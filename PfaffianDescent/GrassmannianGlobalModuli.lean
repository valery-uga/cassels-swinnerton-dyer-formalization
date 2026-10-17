import PfaffianDescent.GrassmannianQuotientNaturality
import PfaffianDescent.GrassmannianSchemeSubmoduleDescent
import PfaffianDescent.GrassmannianQuotientOfBasicCharts

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

/-- The finite projective quotient descended from any finite chart cover of a scheme point. -/
noncomputable def grassmannianSchemeQuotientFromCharts
    {f : GrassmannianAlgebraPoint K A m n} (d : GrassmannianSchemeFiniteChartData K f) :
    Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n :=
  grassmannianQuotientOfBasicCharts A (grassmannianSchemeSubmodule K d)
    d.denominators d.span_eq_top
    (fun a => ⟨d.permutation a, d.matrix a, grassmannianSchemeSubmodule_baseChange K d a⟩)

lemma grassmannianSchemeQuotientFromCharts_point
    {f : GrassmannianAlgebraPoint K A m n} (d : GrassmannianSchemeFiniteChartData K f) :
    grassmannianQuotientAlgebraPoint K (grassmannianSchemeQuotientFromCharts K d) = f := by
  have hr : Set.range (fun a : d.denominators => a.1) = (d.denominators : Set A) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hs : Ideal.span (Set.range (fun a : d.denominators => a.1)) = ⊤ := by
    rw [hr]
    exact d.span_eq_top
  let U := Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of A)
    (fun a : d.denominators => a.1) hs
  apply Subtype.ext
  apply U.openCover.hom_ext
  intro a
  have h := grassmannianQuotientMorphism_pullback_chart K (grassmannianSchemeQuotientFromCharts K d)
    (IsScalarTower.toAlgHom K A (Localization.Away a.1)) (d.permutation a) (d.matrix a)
    (grassmannianSchemeSubmodule_baseChange K d a)
  exact h.trans (d.point_eq a).symm

/-- A scheme point determines its actual finite projective ambient quotient. -/
noncomputable def grassmannianSchemeQuotient (f : GrassmannianAlgebraPoint K A m n) :
    Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n :=
  grassmannianSchemeQuotientFromCharts K (grassmannianSchemeFiniteChartData K f)

lemma grassmannianSchemeQuotient_point (f : GrassmannianAlgebraPoint K A m n) :
    grassmannianQuotientAlgebraPoint K (grassmannianSchemeQuotient K f) = f :=
  grassmannianSchemeQuotientFromCharts_point K _

/-- The quotient Grassmannian represents finite projective quotients over every commutative coefficient algebra. -/
noncomputable def grassmannianGlobalModuliEquiv (A : Type u) [CommRing A] [Algebra K A] (m n : ℕ) :
    GrassmannianAlgebraPoint K A m n ≃ Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n where
  toFun := grassmannianSchemeQuotient K
  invFun := grassmannianQuotientAlgebraPoint K
  left_inv := grassmannianSchemeQuotient_point K
  right_inv W := grassmannianQuotientAlgebraPoint_injective K
    (grassmannianSchemeQuotient_point K (grassmannianQuotientAlgebraPoint K W))

lemma grassmannianGlobalModuliEquiv_chart (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A) :
    grassmannianGlobalModuliEquiv K A m n (grassmannianChartAlgebraPoint K A m n σ T) =
      grassmannianChartQuotient A σ T := by
  apply grassmannianQuotientAlgebraPoint_injective K
  exact (grassmannianSchemeQuotient_point K _).trans
    (grassmannianQuotientAlgebraPoint_chart K σ T).symm

lemma grassmannianGlobalModuliEquiv_naturality
    {B : Type u} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (f : GrassmannianAlgebraPoint K A m n) :
    grassmannianGlobalModuliEquiv K B m n (grassmannianAlgebraPointMap K φ m n f) =
      grassmannianQuotientMap φ.toRingHom (grassmannianGlobalModuliEquiv K A m n f) := by
  apply grassmannianQuotientAlgebraPoint_injective K
  calc
    _ = grassmannianAlgebraPointMap K φ m n f := grassmannianSchemeQuotient_point K _
    _ = grassmannianAlgebraPointMap K φ m n
        (grassmannianQuotientAlgebraPoint K (grassmannianGlobalModuliEquiv K A m n f)) :=
      congrArg (grassmannianAlgebraPointMap K φ m n) (grassmannianSchemeQuotient_point K f).symm
    _ = _ := grassmannianQuotientAlgebraPoint_naturality K _ φ

end
end PfaffianDescent
