import PfaffianDescent.GrassmannianUniversallyClosed
import PfaffianDescent.GrassmannianPointOverlap
import PfaffianDescent.GrassmannianTransitionReflection

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

/-- Two local-algebra-valued Grassmannian points agreeing after an injective coefficient map already agree. -/
theorem grassmannian_local_point_injective
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] S) (hφ : Function.Injective φ)
    (f g : Spec (.of R) ⟶ grassmannianScheme K m n)
    (hf : f ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (hg : g ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (hfg : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) :
    f = g := by
  obtain ⟨i, T, hT⟩ := grassmannian_local_algebra_point K f hf
  obtain ⟨j, U, hU⟩ := grassmannian_local_algebra_point K g hg
  have hS : grassmannianChartEvaluation K (T.map φ) ≫ grassmannianChartι K i =
      grassmannianChartEvaluation K (U.map φ) ≫ grassmannianChartι K j := by
    calc
      grassmannianChartEvaluation K (T.map φ) ≫ grassmannianChartι K i =
          (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianChartEvaluation K T) ≫ grassmannianChartι K i :=
        congrArg (fun a => a ≫ grassmannianChartι K i) (grassmannianChartEvaluation_map K φ T).symm
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f := by rw [Category.assoc, hT]
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g := hfg
      _ = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ grassmannianChartEvaluation K U) ≫ grassmannianChartι K j := by
        rw [Category.assoc, hU]
      _ = _ := congrArg (fun a => a ≫ grassmannianChartι K j) (grassmannianChartEvaluation_map K φ U)
  obtain ⟨hS, he⟩ := grassmannianChartEvaluation_eq_transition K i j (T.map φ) (U.map φ) hS
  obtain ⟨hR, heR⟩ := graphTransitionMatrix_reflect φ.toRingHom hφ (grassmannianChartChange i j) T U hS he
  calc
    f = grassmannianChartEvaluation K T ≫ grassmannianChartι K i := hT.symm
    _ = grassmannianChartEvaluation K (graphTransitionMatrix (grassmannianChartChange i j) T hR) ≫ grassmannianChartι K j :=
      grassmannianChartEvaluation_glue K i j T hR
    _ = grassmannianChartEvaluation K U ≫ grassmannianChartι K j :=
      congrArg (fun T => grassmannianChartEvaluation K T ≫ grassmannianChartι K j) heR
    _ = g := hU

/-- Uniqueness of every valuative lift to the Grassmannian. -/
theorem grassmannianToBase_valuativeUniqueness (m n : ℕ) :
    ValuativeCriterion.Uniqueness (grassmannianToBase K m n) := by
  intro S
  let ψ := Spec.preimage S.i₂
  letI : Algebra K S.R := ψ.hom.toAlgebra
  letI : Algebra K S.K := ((algebraMap S.R S.K).comp ψ.hom).toAlgebra
  letI : IsScalarTower K S.R S.K := IsScalarTower.of_algebraMap_eq' rfl
  have hb : Spec.map (CommRingCat.ofHom (algebraMap K S.R)) = S.i₂ := Spec.map_preimage S.i₂
  refine ⟨fun a b => ?_⟩
  apply CommSq.LiftStruct.ext
  exact grassmannian_local_point_injective K (IsScalarTower.toAlgHom K S.R S.K)
    (IsFractionRing.injective S.R S.K) a.l b.l (a.fac_right.trans hb.symm) (b.fac_right.trans hb.symm)
    (a.fac_left.trans b.fac_left.symm)

end
section
variable (K : Type u) [CommRing K] [IsNoetherianRing K]

instance grassmannianToBase_isSeparated (m n : ℕ) : IsSeparated (grassmannianToBase K m n) :=
  IsSeparated.of_valuativeCriterion _ (grassmannianToBase_valuativeUniqueness K m n)

/-- The Grassmannian structure morphism is proper over every Noetherian coefficient ring. -/
instance grassmannianToBase_isProper (m n : ℕ) : IsProper (grassmannianToBase K m n) := by
  exact ⟨⟩

end
end PfaffianDescent
