import PfaffianDescent.GrassmannianScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

instance grassmannianChartToBase_smooth (m n : ℕ) : Smooth (grassmannianChartToBase K m n) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  change Algebra.Smooth K (MvPolynomial (Fin n × Fin m) K)
  exact ⟨inferInstance, inferInstance⟩

/-- The chart structure morphisms glue to a structure morphism for the global scheme. -/
noncomputable def grassmannianToBase (m n : ℕ) : grassmannianScheme K m n ⟶ Spec (.of K) :=
  Multicoequalizer.desc (grassmannianGlueData K m n).toGlueData.diagram _
    (fun _ => grassmannianChartToBase K m n) (by
      rintro ⟨i, j⟩
      change grassmannianAtlasι K i.down j.down ≫ grassmannianChartToBase K m n =
        (grassmannianAtlasTransition K i.down j.down ≫ grassmannianAtlasι K j.down i.down) ≫
          grassmannianChartToBase K m n
      rw [grassmannianAtlasTransition_ι]
      exact (grassmannianOverlapOtherι_toBase K _).symm)

lemma grassmannianChartι_toBase {m n : ℕ} (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianChartι K i ≫ grassmannianToBase K m n = grassmannianChartToBase K m n := by
  unfold grassmannianToBase
  exact Multicoequalizer.π_desc (grassmannianGlueData K m n).toGlueData.diagram _ _ _ (ULift.up i)

/-- Smoothness of the global glued Grassmannian follows from its affine chart cover. -/
instance grassmannianToBase_smooth (m n : ℕ) : Smooth (grassmannianToBase K m n) := by
  let 𝒰 := (grassmannianGlueData K m n).openCover
  letI (i : 𝒰.I₀) : IsAffine (𝒰.X i) :=
    inferInstanceAs (IsAffine (Spec (.of (GrassmannianChartRing K m n))))
  apply HasRingHomProperty.of_source_openCover (P := @Smooth.{u}) 𝒰
  intro i
  have hs : Smooth (𝒰.f i ≫ grassmannianToBase K m n) := by
    change Smooth (grassmannianChartι K i.down ≫ grassmannianToBase K m n)
    rw [grassmannianChartι_toBase]
    infer_instance
  exact HasRingHomProperty.appTop @Smooth _ hs

end
end PfaffianDescent
