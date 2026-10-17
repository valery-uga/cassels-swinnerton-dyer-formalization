import PfaffianDescent.GrassmannianLocalCharts
import PfaffianDescent.GrassmannianAlgebraPoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable (R : Type*) [CommRing R] {m n : ℕ}

noncomputable def grassmannianChartQuotientEquiv (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    (((Fin m → R) × (Fin n → R)) ⧸ grassmannianChartSubmodule R σ T) ≃ₗ[R] (Fin n → R) :=
  (Submodule.Quotient.equiv (Matrix.toLin' T).graph (grassmannianChartSubmodule R σ T)
    (graphCoordinatePermutation R σ.symm) rfl).symm.trans (graphQuotientEquiv (Matrix.toLin' T))

/-- The actual finite projective quotient represented by a point in any coordinate chart. -/
noncomputable def grassmannianChartQuotient (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n where
  toSubmodule := grassmannianChartSubmodule R σ T
  finite_quotient := Module.Finite.equiv (grassmannianChartQuotientEquiv R σ T).symm
  projective_quotient := Module.Projective.of_equiv (grassmannianChartQuotientEquiv R σ T).symm
  rankAtStalk_eq p := by
    have : Nontrivial R := (algebraMap R (Localization.AtPrime p.asIdeal)).domain_nontrivial
    rw [Module.rankAtStalk_eq_of_equiv (grassmannianChartQuotientEquiv R σ T),
      Module.rankAtStalk_eq_finrank_of_free]
    simp

end
section
variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] (m n : ℕ)

abbrev GrassmannianAlgebraPoint :=
  {f : Spec (.of A) ⟶ grassmannianScheme K m n //
    f ≫ grassmannianToBase K m n = Spec.map (CommRingCat.ofHom (algebraMap K A))}

noncomputable def grassmannianChartAlgebraPoint (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A) : GrassmannianAlgebraPoint K A m n :=
  ⟨grassmannianChartEvaluation K T ≫ grassmannianChartι K σ, by
    rw [Category.assoc, grassmannianChartι_toBase]
    exact grassmannianChartEvaluation_toBase K T⟩

lemma grassmannianChartAlgebraPoint_eq_iff (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (T U : Matrix (Fin n) (Fin m) A) :
    grassmannianChartAlgebraPoint K A m n σ T = grassmannianChartAlgebraPoint K A m n τ U ↔
      grassmannianChartQuotient A σ T = grassmannianChartQuotient A τ U := by
  constructor
  · intro h
    apply Module.Grassmannian.ext
    exact (grassmannianChartEvaluation_eq_iff_submodule K σ τ T U).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (grassmannianChartEvaluation_eq_iff_submodule K σ τ T U).mpr
      (congrArg Module.Grassmannian.toSubmodule h)

variable [IsLocalRing A]

lemma grassmannianChartAlgebraPoint_surjective :
    Function.Surjective (fun p : Equiv.Perm (Fin m ⊕ Fin n) × Matrix (Fin n) (Fin m) A =>
      grassmannianChartAlgebraPoint K A m n p.1 p.2) := by
  intro p
  obtain ⟨σ, T, hT⟩ := grassmannian_local_algebra_point K p.1 p.2
  exact ⟨(σ, T), Subtype.ext hT⟩

lemma grassmannianChartQuotient_surjective :
    Function.Surjective (fun p : Equiv.Perm (Fin m ⊕ Fin n) × Matrix (Fin n) (Fin m) A =>
      grassmannianChartQuotient A p.1 p.2) := by
  intro W
  obtain ⟨σ, T, hT⟩ := grassmannian_local_exists_graph A W
  exact ⟨(σ, T), Module.Grassmannian.ext hT.symm⟩

/-- Scheme-valued points over every local coefficient algebra are exactly the locally free quotients. -/
noncomputable def grassmannianLocalModuliEquiv :
    GrassmannianAlgebraPoint K A m n ≃ Module.Grassmannian A ((Fin m → A) × (Fin n → A)) n := by
  let f := fun p : Equiv.Perm (Fin m ⊕ Fin n) × Matrix (Fin n) (Fin m) A =>
    grassmannianChartAlgebraPoint K A m n p.1 p.2
  let g := fun p : Equiv.Perm (Fin m ⊕ Fin n) × Matrix (Fin n) (Fin m) A =>
    grassmannianChartQuotient A p.1 p.2
  have hf : Function.Surjective f := grassmannianChartAlgebraPoint_surjective K A m n
  have hg : Function.Surjective g := grassmannianChartQuotient_surjective A m n
  let d := Function.surjInv hf
  have hd (p) : f (d p) = p := Function.surjInv_eq hf p
  have hfg (p q) : f p = f q ↔ g p = g q := grassmannianChartAlgebraPoint_eq_iff K A m n p.1 q.1 p.2 q.2
  apply Equiv.ofBijective (g ∘ d)
  constructor
  · intro p q h
    have he := (hfg (d p) (d q)).mpr h
    simpa only [hd] using he
  · intro W
    obtain ⟨p, hp⟩ := hg W
    refine ⟨f p, ?_⟩
    exact ((hfg (d (f p)) p).mp (hd (f p))).trans hp


lemma grassmannianLocalModuliEquiv_chart (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A) :
    grassmannianLocalModuliEquiv K A m n (grassmannianChartAlgebraPoint K A m n σ T) =
      grassmannianChartQuotient A σ T := by
  let p := Function.surjInv (grassmannianChartAlgebraPoint_surjective K A m n)
    (grassmannianChartAlgebraPoint K A m n σ T)
  change grassmannianChartQuotient A p.1 p.2 = grassmannianChartQuotient A σ T
  apply (grassmannianChartAlgebraPoint_eq_iff K A m n p.1 σ p.2 T).mp
  exact Function.surjInv_eq (grassmannianChartAlgebraPoint_surjective K A m n) _

end
end PfaffianDescent
