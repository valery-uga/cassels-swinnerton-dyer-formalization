import PfaffianDescent.ClosedImmersionCohomologyOneLinearInjection
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! SOURCE ONLY / UNVERIFIED. Specialize the genuine closed-immersion H1
injection to the ORIGINAL homogeneous ideal I. The original source action
is toBase I and the independent ambient action is ambientToBase. Their
relation is the proved actual quotientProjMap_toBase, not an action premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual ORIGINAL-K linear injection into the actual ambient closed
pushforward H1. The witness is the canonical map from the preceding module;
only the true original embedding square is used to identify scalar actions. -/
theorem homogeneousProjectiveClosedImmersion_cohomologyOneLinearInjection
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [HasExt.{u} (scheme I).Modules]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (M : (scheme I).Modules) :
    letI : Linear K (scheme I).Modules := schemeModulesLinearOver (toBase I)
    letI : Linear K (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
      schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    ∃ T : schemeModuleCohomology (scheme I) M 1 →ₗ[K]
        schemeModuleCohomology (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
          ((Scheme.Modules.pushforward (quotientProjMap I)).obj M) 1,
      Function.Injective T := by
  have h :
      letI : Linear K (scheme I).Modules := schemeModulesLinearOver
        (quotientProjMap I ≫ ambientToBase (R := K) (σ := Fin 4))
      letI : Linear K (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
        schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
      ∃ T : schemeModuleCohomology (scheme I) M 1 →ₗ[K]
          schemeModuleCohomology (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
            ((Scheme.Modules.pushforward (quotientProjMap I)).obj M) 1,
        Function.Injective T := by
    exact ⟨closedImmersion_cohomologyOneLinearMap
        (ambientToBase (R := K) (σ := Fin 4)) (quotientProjMap I) M,
      closedImmersion_cohomologyOneLinearMap_injective
        (ambientToBase (R := K) (σ := Fin 4)) (quotientProjMap I) M⟩
  -- Transport the whole scalar-dependent proposition along the actual square.
  -- Both actions are still constructed independently from their base maps.
  let P : ((scheme I) ⟶ Spec (CommRingCat.of K)) → Prop := fun pi =>
    letI : Linear K (scheme I).Modules := schemeModulesLinearOver pi
    letI : Linear K (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
      schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    ∃ T : schemeModuleCohomology (scheme I) M 1 →ₗ[K]
        schemeModuleCohomology (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
          ((Scheme.Modules.pushforward (quotientProjMap I)).obj M) 1,
      Function.Injective T
  have hP : P (quotientProjMap I ≫ ambientToBase (R := K) (σ := Fin 4)) := h
  have hbase : quotientProjMap I ≫ ambientToBase (R := K) (σ := Fin 4) = toBase I :=
    quotientProjMap_toBase I
  change P (toBase I)
  exact Eq.mp (congrArg P hbase) hP

/-- Native finite ambient H1 implies native intrinsic H1, both over the
ORIGINAL K. In particular I can be the literal p/q intersection ideal and
M its actual curve unit. No desired injection or scalar comparison is an
input, and no exactness of the homogeneous closed immersion's pullback is
used. -/
theorem homogeneousProjectiveClosedImmersion_cohomology_one_finite_of_pushforward
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [HasExt.{u} (scheme I).Modules]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    (M : (scheme I).Modules) :
    letI : Linear K (scheme I).Modules := schemeModulesLinearOver (toBase I)
    letI : Linear K (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
      schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K
      (schemeModuleCohomology (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
        ((Scheme.Modules.pushforward (quotientProjMap I)).obj M) 1) →
    Module.Finite K (schemeModuleCohomology (scheme I) M 1) := by
  letI : Linear K (scheme I).Modules := schemeModulesLinearOver (toBase I)
  letI : Linear K (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  intro hfinite
  letI := hfinite
  obtain ⟨T, hT⟩ := homogeneousProjectiveClosedImmersion_cohomologyOneLinearInjection I M
  exact Module.Finite.of_injective T hT

end PfaffianDescent.Coray
