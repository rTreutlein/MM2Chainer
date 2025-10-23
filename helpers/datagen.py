#!/usr/bin/env python3
"""
Synthetic ATP data generator.

Emits S-expr style facts/rules like:
  (Implication (Animal $x) (Dog $x) (STV 0.73 0.92))
  (Implication (Dog $x) (ShortHair $x) (STV 0.61 0.85))
  (Dog dog1)
  (ShortHair dog1)

Usage:
  python gen_atp_data.py > kb.nal
"""

import random
from typing import List, Tuple

# --------------------------
# CONFIG
# --------------------------
SEED = 42

# Number of distinct animal subtypes (besides the generic 'Animal')
NUM_SUBTYPES = 8

# Number of distinct properties to scatter across subtypes
NUM_PROPERTIES = 50

# How many properties each subtype tends to “imply”
PROPS_PER_SUBTYPE_MIN = 5
PROPS_PER_SUBTYPE_MAX = 10

# Number of individuals to generate
NUM_INDIVIDUALS = 50

# Chance an individual gets an explicit subtype fact (beyond just Animal)
# When chosen, which subtype(s) are added depends on the Animal->Subtype STV
SUBTYPE_FACT_RATE = 0.85   # 0..1

# Chance to emit a property fact for an individual given (Subtype x)
# This is scaled by the subtype->property STV "strength"
BASE_PROPERTY_FACT_RATE = 0.8  # 0..1

# Ranges for generating STV strengths/confidences
# (strength ~ how often the rule holds; confidence ~ reliability of that estimate)
STRENGTH_RANGE = (0.5, 0.95)
CONFIDENCE_RANGE = (0.7, 0.99)

# Optional: add a small fraction of contradictory/noisy property facts
NOISE_PROPERTY_RATE = 0.03  # probability to flip/include a property contrary to expectations

# Optional: deterministic, readable predicate name seeds
SUBTYPE_SEED_WORDS = [
    "Dog", "Cat", "Horse", "Bird", "Rabbit", "Sheep", "Goat", "Cow",
    "Pig", "Wolf", "Fox", "Bear", "Deer", "Lion", "Tiger", "Dolphin",
]
PROPERTY_SEED_WORDS = [
    "ShortHair", "LongHair", "Brown", "Black", "White", "Spotted", "Striped",
    "HasTail", "HasHorns", "Nocturnal", "Aquatic", "FastRunner", "Barks",
    "Meows", "Claws", "Hooved",
]

# --------------------------
# HELPER GENERATION
# --------------------------

def sample_stv() -> Tuple[float, float]:
    s = random.uniform(*STRENGTH_RANGE)
    c = random.uniform(*CONFIDENCE_RANGE)
    return round(s, 2), round(c, 2)

def choose_names(seed_words: List[str], n: int) -> List[str]:
    # deterministically pick n distinct names, falling back to generated ones
    pool = seed_words[:]
    random.shuffle(pool)
    names = pool[: min(n, len(pool))]
    while len(names) < n:
        names.append(f"Type{len(names)+1}")
    return names

def unique_pairs(xs: List[str], k_min: int, k_max: int) -> List[Tuple[str, List[str]]]:
    """For each x in xs pick between k_min..k_max distinct partners from a global property list later."""
    # This helper just allocates counts; actual property binding is later.
    result = []
    for x in xs:
        k = random.randint(k_min, k_max)
        result.append((x, k))
    return result

def sample_categorical_strengths(labels: List[str], concentration: float = 1.5) -> List[Tuple[str, float]]:
    """Sample a categorical distribution over labels that sums to 1.0 (within rounding)."""
    if not labels:
        return []
    weights = [random.gammavariate(concentration, 1.0) for _ in labels]
    total = sum(weights)
    if total == 0:
        # degenerate case; fall back to uniform
        strengths = [1.0 / len(labels)] * len(labels)
    else:
        strengths = [w / total for w in weights]

    # Snap to two decimal places while keeping the distribution normalized.
    ints = [max(1, round(s * 100)) for s in strengths]
    total_int = sum(ints)

    # Reduce any surplus while keeping probabilities >= 0.01
    while total_int > 100:
        idx = max(
            (i for i in range(len(ints)) if ints[i] > 1),
            key=lambda i: ints[i],
            default=None,
        )
        if idx is None:
            break
        ints[idx] -= 1
        total_int -= 1

    # Distribute any deficit starting with the smallest entries
    while total_int < 100:
        idx = min(range(len(ints)), key=lambda i: ints[i])
        ints[idx] += 1
        total_int += 1

    strengths = [i / 100 for i in ints]
    return list(zip(labels, strengths))

def sample_fact_stv(strength_hint: float = 0.95, conf_hint: float = 0.9, spread: float = 0.05) -> Tuple[float, float]:
    """Generate an STV for ground facts, centered around the provided hints."""
    strength = max(0.01, min(0.99, random.gauss(strength_hint, spread)))
    confidence = max(0.5, min(0.99, random.gauss(conf_hint, spread)))
    return round(strength, 2), round(confidence, 2)

# --------------------------
# MAIN GENERATION
# --------------------------

def main():
    random.seed(SEED)

    # 1) Define predicates
    subtypes = choose_names(SUBTYPE_SEED_WORDS, NUM_SUBTYPES)
    properties = choose_names(PROPERTY_SEED_WORDS, NUM_PROPERTIES)

    # 2) Create Animal -> Subtype implication rules with STVs
    animal_to_subtype_rules = []
    for t, s in sample_categorical_strengths(subtypes):
        c = round(random.uniform(*CONFIDENCE_RANGE), 2)
        animal_to_subtype_rules.append((t, s, c))

    # 3) For each subtype, assign 2..4 properties and make Subtype -> Property implication rules
    subtype_prop_counts = unique_pairs(subtypes, PROPS_PER_SUBTYPE_MIN, PROPS_PER_SUBTYPE_MAX)

    # distribute properties roughly evenly but randomly
    props_queue = properties[:]
    random.shuffle(props_queue)
    subtype_to_props = {}
    for t, k in subtype_prop_counts:
        if k >= len(props_queue):  # recycle if exhausted
            props_queue = properties[:]
            random.shuffle(props_queue)
        chosen = random.sample(props_queue, k)
        subtype_to_props[t] = chosen

    subtype_to_prop_rules = []  # list of (subtype, property, s, c)
    for t, props in subtype_to_props.items():
        for p in props:
            s, c = sample_stv()
            subtype_to_prop_rules.append((t, p, s, c))

    # 4) Emit RULES
    print("; ---------------------")
    print("; RULES: Animal -> Subtype typicality")
    print("; ---------------------")
    print()
    for idx, (t, s, c) in enumerate(animal_to_subtype_rules, 1):
        rule_name = f"rule-animal-{idx:02d}"
        expr = f"(Implication (Animal $x) ({t} $x))"
        print(f"(: {rule_name} {expr} (STV {s:.2f} {c:.2f}))")

    print()
    print("; ---------------------")
    print("; RULES: Subtype -> Property typicality")
    print("; ---------------------")
    print()
    for idx, (t, p, s, c) in enumerate(subtype_to_prop_rules, 1):
        rule_name = f"rule-prop-{idx:03d}"
        expr = f"(Implication ({t} $x) ({p} $x))"
        print(f"(: {rule_name} {expr} (STV {s:.2f} {c:.2f}))")

    # 5) Generate individuals & ground facts
    # Strategy:
    #   - Always assert (Animal ai)
    #   - With probability SUBTYPE_FACT_RATE, sample exactly one subtype for ai based on the
    #       categorical Animal->Subtype strengths (they sum to 1.0).
    #   - For each asserted subtype, add properties based on its Subtype->Property strengths,
    #       scaled by BASE_PROPERTY_FACT_RATE.
    #   - Add a small amount of noise property facts.
    print()
    print("; ---------------------")
    print("; FACTS: Individuals")
    print("; ---------------------")

    # Precompute maps for quick sampling
    subtype_strength = {t: s for t, s, _c in animal_to_subtype_rules}
    subtype_props = {t: [] for t in subtypes}
    for t, p, s, c in subtype_to_prop_rules:
        subtype_props[t].append((p, s))
    subtype_weights = [subtype_strength[t] for t in subtypes]

    individuals = []
    for i in range(1, NUM_INDIVIDUALS + 1):
        # give some readable names: a mix of 'dogN', subtypeN, or generic aN
        if i <= len(subtypes):
            name = f"{subtypes[i-1].lower()}{i}"
        else:
            name = f"a{i}"
        individuals.append(name)

    fact_counter = 1

    print()
    for name in individuals:
        stv_animal = sample_fact_stv(0.99, 0.95, 0.01)
        print(f"(: fact-{fact_counter:04d} (Animal {name}) (STV {stv_animal[0]:.2f} {stv_animal[1]:.2f}))")
        fact_counter += 1

        chosen_subtypes = []
        if random.random() < SUBTYPE_FACT_RATE:
            chosen_subtype = random.choices(subtypes, weights=subtype_weights, k=1)[0]
            chosen_subtypes.append(chosen_subtype)

        # Ensure at least one subtype sometimes, but not always, to keep variety
        if not chosen_subtypes and random.random() < 0.4:
            chosen_subtypes.append(random.choices(subtypes, weights=subtype_weights, k=1)[0])

        for t in chosen_subtypes:
            stv_subtype = sample_fact_stv(subtype_strength[t], 0.9, 0.04)
            print(f"(: fact-{fact_counter:04d} ({t} {name}) (STV {stv_subtype[0]:.2f} {stv_subtype[1]:.2f}))")
            fact_counter += 1
            # properties implied by this subtype
            for (p, s_prop) in subtype_props.get(t, []):
                emit_p = BASE_PROPERTY_FACT_RATE * s_prop
                if random.random() < emit_p:
                    stv_prop = sample_fact_stv(s_prop, 0.85, 0.05)
                    print(f"(: fact-{fact_counter:04d} ({p} {name}) (STV {stv_prop[0]:.2f} {stv_prop[1]:.2f}))")
                    fact_counter += 1

        # Noise properties (picked from global set)
        if random.random() < NOISE_PROPERTY_RATE:
            p = random.choice(properties)
            # avoid duplicating if it was already emitted; still okay if it is
            stv_noise = sample_fact_stv(0.3, 0.6, 0.08)
            print(f"(: fact-{fact_counter:04d} ({p} {name}) (STV {stv_noise[0]:.2f} {stv_noise[1]:.2f}))")
            fact_counter += 1

if __name__ == "__main__":
    main()
