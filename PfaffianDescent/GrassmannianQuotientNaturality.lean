import PfaffianDescent.GrassmannianQuotientMorphism
import PfaffianDescent.GrassmannianLocalization

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {A B : Type u} [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] {m n : ℕ}
  (W : Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n)

/-- A quotient's global morphism is the expected chart wherever its base change is a graph. -/
lemma grassmannianQuotientMorphism_pullback_chart (φ : A →ₐ[K] B)
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) B)
    (hT : grassmannianSubmoduleBaseChange φ.toRingHom W.toSubmodule =
      grassmannianChartSubmodule B σ T) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianQuotientMorphism K W =
      (grassmannianChartAlgebraPoint K B m n σ T).1 := by
  let U := grassmannianQuotientOpenCover W
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  apply Scheme.Cover.hom_ext (U.pullback₁ f)
  intro p
  have hc := grassmannianChart_morphism_eq_of_baseChange K
    (IsScalarTower.toAlgHom K A (Localization.Away (grassmannianBasicChartAt W p).denominator))
    φ W.toSubmodule (grassmannianBasicChartAt W p).permutation σ
    (grassmannianBasicChartAt W p).matrix T (grassmannianBasicChartAt W p).submodule_eq hT
    ((U.pullback₁ f).X p) (U.pullbackHom f p) ((U.pullback₁ f).f p)
    (U.pullbackHom_map f p)
  calc
    (U.pullback₁ f).f p ≫ (f ≫ grassmannianQuotientMorphism K W) =
        (U.pullbackHom f p) ≫ (U.f p ≫ grassmannianQuotientMorphism K W) := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ grassmannianQuotientMorphism K W)
          (U.pullbackHom_map f p).symm).trans (Category.assoc _ _ _))
    _ = (U.pullbackHom f p) ≫ grassmannianQuotientChartMorphism K W p :=
      congrArg (fun q => U.pullbackHom f p ≫ q) (grassmannianQuotientMorphism_onCover K W p)
    _ = (U.pullback₁ f).f p ≫ (grassmannianChartAlgebraPoint K B m n σ T).1 := hc

/-- The global quotient-to-scheme map commutes with arbitrary coefficient homomorphisms. -/
theorem grassmannianQuotientMorphism_naturality (φ : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianQuotientMorphism K W =
      grassmannianQuotientMorphism K (grassmannianQuotientMap φ.toRingHom W) := by
  let Z := grassmannianQuotientMap φ.toRingHom W
  apply (grassmannianQuotientOpenCover Z).hom_ext
  intro p
  let ψ := IsScalarTower.toAlgHom K B (Localization.Away (grassmannianBasicChartAt Z p).denominator)
  have hT : grassmannianSubmoduleBaseChange (ψ.comp φ).toRingHom W.toSubmodule =
      grassmannianChartSubmodule _ (grassmannianBasicChartAt Z p).permutation
        (grassmannianBasicChartAt Z p).matrix := by
    change grassmannianSubmoduleBaseChange (ψ.toRingHom.comp φ.toRingHom) W.toSubmodule = _
    rw [← grassmannianSubmoduleBaseChange_comp]
    exact (grassmannianBasicChartAt Z p).submodule_eq
  have hc := grassmannianQuotientMorphism_pullback_chart K W (ψ.comp φ) _ _ hT
  have hl : (grassmannianQuotientOpenCover Z).f p ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianQuotientMorphism K W) =
        grassmannianQuotientChartMorphism K Z p := by
    change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianQuotientMorphism K W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    exact hc
  exact hl.trans (grassmannianQuotientMorphism_onCover K Z p).symm

lemma grassmannianQuotientAlgebraPoint_naturality (φ : A →ₐ[K] B) :
    grassmannianAlgebraPointMap K φ m n (grassmannianQuotientAlgebraPoint K W) =
      grassmannianQuotientAlgebraPoint K (grassmannianQuotientMap φ.toRingHom W) := by
  apply Subtype.ext
  exact grassmannianQuotientMorphism_naturality K W φ

/-- On every local base, global classification recovers exactly the original finite projective quotient. -/
lemma grassmannianQuotientAlgebraPoint_local [IsLocalRing A] :
    grassmannianLocalModuliEquiv K A m n (grassmannianQuotientAlgebraPoint K W) = W := by
  obtain ⟨⟨σ, T⟩, rfl⟩ := grassmannianChartQuotient_surjective A m n W
  rw [grassmannianQuotientAlgebraPoint_chart, grassmannianLocalModuliEquiv_chart]

/-- The global map is injective on actual quotients over every commutative coefficient algebra. -/
theorem grassmannianQuotientAlgebraPoint_injective :
    Function.Injective (grassmannianQuotientAlgebraPoint K (A := A) (m := m) (n := n)) := by
  intro W Z h
  apply Module.Grassmannian.ext
  apply grassmannianSubmodule_eq_of_localization A
  intro p
  let φ := IsScalarTower.toAlgHom K A (Localization.AtPrime p.asIdeal)
  have he := congrArg (grassmannianAlgebraPointMap K φ m n) h
  rw [grassmannianQuotientAlgebraPoint_naturality, grassmannianQuotientAlgebraPoint_naturality] at he
  have hq := congrArg (grassmannianLocalModuliEquiv K (Localization.AtPrime p.asIdeal) m n) he
  rw [grassmannianQuotientAlgebraPoint_local, grassmannianQuotientAlgebraPoint_local] at hq
  exact congrArg Module.Grassmannian.toSubmodule hq

end
end PfaffianDescent
