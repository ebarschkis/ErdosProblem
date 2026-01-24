import argparse
import bisect
import math
import random
from typing import Dict, List, Optional, Tuple


def k_n(n: int) -> int:
    return 4 + math.ceil(math.log2(math.log2(n + 16)))


def build_sequences(n_max: int) -> Tuple[List[int], List[int]]:
    k_list = []
    m_list = [10]
    for n in range(n_max + 1):
        k = k_n(n)
        k_list.append(k)
        m_next = (((2**k) * 2 - 3) * m_list[n]) // 2
        m_list.append(m_next)
    return k_list, m_list


def build_block(m_n: int, k: int) -> List[int]:
    block = [m_n * (2**i) for i in range(k - 1)]
    block.append((2 ** (k - 1) - 1) * m_n + 1)
    return block


def build_blocks(m_list: List[int], k_list: List[int]) -> List[List[int]]:
    return [build_block(m_list[n], k_list[n]) for n in range(len(k_list))]


def build_sequence(blocks: List[List[int]]) -> List[int]:
    return [x for block in blocks for x in block]


def b_n_set(m_n: int, k: int) -> List[int]:
    b_set = [j * m_n for j in range(0, 2 ** (k - 1))]
    b_set += [j * m_n + 1 for j in range(2 ** (k - 1), 2**k - 1)]
    return sorted(set(b_set))


def greedy_digit(x: int, b_list: List[int]) -> int:
    idx = bisect.bisect_right(b_list, x)
    return b_list[idx - 1]


def greedy_expansion(
    m: int, n0: int, n_max: int, b_lists: Dict[int, List[int]]
) -> Tuple[List[int], int]:
    r = m
    digits = []
    for n in range(n_max, n0 - 1, -1):
        b_n = greedy_digit(r, b_lists[n])
        digits.append(b_n)
        r -= b_n
    digits.reverse()
    return digits, r


def block_subset_sums(block: List[int], max_sum: int) -> int:
    bits = 1
    mask = (1 << (max_sum + 1)) - 1
    for a in block:
        bits |= bits << a
        bits &= mask
    return bits


def all_subset_sums(blocks: List[List[int]], max_sum: int) -> int:
    bits = 1
    mask = (1 << (max_sum + 1)) - 1
    for block in blocks:
        for a in block:
            if a > max_sum:
                continue
            bits |= bits << a
            bits &= mask
    return bits


def check_block_scales(m_list: List[int], k_list: List[int], n_max: int) -> None:
    for n in range(n_max + 1):
        k = k_list[n]
        m_n = m_list[n]
        m_next = m_list[n + 1]
        left = (2**k - 2) * m_n
        right = (2**k - 1) * m_n
        if not (left < m_next < right):
            raise AssertionError(
                f"(1) fails at n={n}: {left} < {m_next} < {right}"
            )


def check_block_ratios(m_list: List[int], k_list: List[int], n_max: int) -> None:
    for n in range(n_max + 1):
        k = k_list[n]
        m_n = m_list[n]
        inner_ratio = 2.0
        final_ratio = ((2 ** (k - 1) - 1) * m_n + 1) / (2 ** (k - 2) * m_n)
        final_formula = 2 - 1 / (2 ** (k - 2)) + 1 / (2 ** (k - 2) * m_n)
        if abs(final_ratio - final_formula) > 1e-12:
            raise AssertionError(f"final ratio formula mismatch at n={n}")
        if abs(inner_ratio - 2.0) > 1e-12:
            raise AssertionError(f"inner ratio mismatch at n={n}")

        if n + 1 < len(m_list):
            boundary_ratio = m_list[n + 1] / ((2 ** (k - 1) - 1) * m_n + 1)
            if boundary_ratio <= 0:
                raise AssertionError(f"boundary ratio nonpositive at n={n}")


def check_sequence_properties(blocks: List[List[int]]) -> Tuple[float, float]:
    seq = build_sequence(blocks)
    for i in range(1, len(seq)):
        if seq[i] < seq[i - 1]:
            raise AssertionError("Sequence is not nondecreasing")

    max_final_dev = 0.0
    max_boundary_dev = 0.0
    idx = 0
    for block in blocks:
        for j in range(len(block) - 2):
            if block[j + 1] != 2 * block[j]:
                raise AssertionError("Inner ratio not equal to 2")
        final_ratio = block[-1] / block[-2]
        max_final_dev = max(max_final_dev, abs(final_ratio - 2.0))
        idx += len(block)
        if idx < len(seq):
            boundary_ratio = seq[idx] / seq[idx - 1]
            max_boundary_dev = max(max_boundary_dev, abs(boundary_ratio - 2.0))
    return max_final_dev, max_boundary_dev


def check_b_n_properties(m_list: List[int], k_list: List[int], n_max: int) -> None:
    for n in range(n_max + 1):
        k = k_list[n]
        m_n = m_list[n]
        b_list = b_n_set(m_n, k)
        c_n = (2 ** (k - 1) - 1) * m_n
        if len(b_list) != 2**k - 1:
            raise AssertionError(f"|B_n| mismatch at n={n}")
        if c_n not in b_list:
            raise AssertionError(f"c_n not in B_n at n={n}")
        if c_n + 1 in b_list:
            raise AssertionError(f"c_n+1 unexpectedly in B_n at n={n}")
        if max(b_list) >= m_list[n + 1]:
            raise AssertionError(f"B_n not subset [0, M_{n+1}) at n={n}")


def check_greedy_covering(m_list: List[int], k_list: List[int], n_max: int) -> None:
    for n in range(n_max + 1):
        k = k_list[n]
        m_n = m_list[n]
        m_next = m_list[n + 1]
        b_list = b_n_set(m_n, k)
        for x in range(m_next + 1):
            b = greedy_digit(x, b_list)
            if not (0 <= x - b <= m_n):
                raise AssertionError(f"greedy covering fails at n={n}, x={x}")


def check_greedy_expansion_and_correction(
    m_list: List[int],
    k_list: List[int],
    n0: int,
    n_max: int,
    max_m: int,
) -> Tuple[int, int]:
    b_lists = {n: b_n_set(m_list[n], k_list[n]) for n in range(n0, n_max + 1)}
    c_list = {n: (2 ** (k_list[n] - 1) - 1) * m_list[n] for n in range(n0, n_max + 1)}
    blocks = [build_block(m_list[n], k_list[n]) for n in range(n0, n_max + 1)]
    bitset = all_subset_sums(blocks, max_m)
    mask = (1 << (max_m + 1)) - 1
    present = (bitset & mask).bit_count()
    exceptions = (max_m + 1) - present

    correction_failures = 0
    for m in range(max_m + 1):
        digits, d = greedy_expansion(m, n0, n_max, b_lists)
        if not (0 <= d <= m_list[n0]):
            raise AssertionError(f"greedy remainder out of range for m={m}")
        if sum(digits) + d != m:
            raise AssertionError(f"greedy expansion sum mismatch for m={m}")
        special = 0
        for idx, n in enumerate(range(n0, n_max + 1)):
            if digits[idx] == c_list[n]:
                special += 1
        if special >= m_list[n0]:
            if ((bitset >> m) & 1) == 0:
                correction_failures += 1

    if correction_failures != 0:
        raise AssertionError(f"correction lemma failed for {correction_failures} values")
    return exceptions, max_m


def subset_sums_half(values: List[int]) -> List[int]:
    sums = [0]
    for v in values:
        sums += [s + v for s in sums]
    return sums


def estimate_density_sampling(
    blocks: List[List[int]],
    n0: int,
    n_max: int,
    upper: int,
    samples: int,
    seed: int,
) -> float:
    values = []
    for n in range(n0, n_max + 1):
        for v in blocks[n]:
            if v <= upper:
                values.append(v)
    mid = len(values) // 2
    left = subset_sums_half(values[:mid])
    right = subset_sums_half(values[mid:])
    right_set = set(right)

    rng = random.Random(seed)
    hits = 0
    for _ in range(samples):
        m = rng.randint(0, upper)
        found = False
        for s in left:
            if (m - s) in right_set:
                found = True
                break
        if found:
            hits += 1
    return hits / samples


def exceptions_upper_bound(
    m_list: List[int], k_list: List[int], n0: int, n_max: int
) -> Tuple[int, float]:
    m_n0 = m_list[n0]
    dp = [0] * m_n0
    dp[0] = 1
    for n in range(n0, n_max + 1):
        s_n = 2 ** k_list[n] - 1
        new = [0] * m_n0
        new[0] = dp[0] * (s_n - 1)
        for j in range(1, m_n0):
            new[j] = dp[j] * (s_n - 1) + dp[j - 1]
        dp = new
    exceptions = (m_n0 + 1) * sum(dp)
    ratio = exceptions / m_list[n_max + 1]
    return exceptions, ratio


def run(
    n_max: int,
    n0: int,
    max_m: Optional[int],
    samples: int,
    seed: int,
) -> None:
    k_list, m_list = build_sequences(n_max)
    blocks = [build_block(m_list[n], k_list[n]) for n in range(n_max + 1)]

    check_block_scales(m_list, k_list, n_max)
    check_block_ratios(m_list, k_list, n_max)
    check_b_n_properties(m_list, k_list, n_max)

    max_final_dev, max_boundary_dev = check_sequence_properties(blocks)

    m_cap = m_list[n_max + 1]
    if max_m is not None:
        m_cap = min(m_cap, max_m)

    greedy_covering_limit = -1
    for n in range(n_max + 1):
        if m_list[n + 1] <= m_cap:
            greedy_covering_limit = n
    if greedy_covering_limit >= 0:
        check_greedy_covering(m_list, k_list, greedy_covering_limit)

    exceptions, denom = check_greedy_expansion_and_correction(
        m_list, k_list, n0, n_max, m_cap
    )
    density = 1 - exceptions / (denom + 1)

    print("Block lengths k_n and scales M_n:")
    for n in range(n_max + 1):
        log_term = math.log2(n + 16)
        print(
            f"n={n} k_n={k_list[n]} 2^k/log2(n+16)={2**k_list[n]/log_term:.3f} "
            f"M_n={m_list[n]} M_{n+1}={m_list[n+1]}"
        )
    print("")
    print(
        f"Max |ratio-2| inside blocks (final step only): {max_final_dev:.6e}"
    )
    print(f"Max |ratio-2| at boundaries: {max_boundary_dev:.6e}")
    if greedy_covering_limit >= 0:
        print("Greedy covering checked for n <= ", greedy_covering_limit)
    else:
        print("Greedy covering skipped (m_cap too small for full range).")
    print(f"E_N={exceptions} out of {denom + 1} -> density {density:.6f}")
    bound_exc, bound_ratio = exceptions_upper_bound(m_list, k_list, n0, n_max)
    print(
        f"Upper bound E_N/M_{n_max + 1}: {bound_ratio:.6e} (E_N <= {bound_exc})"
    )
    if samples > 0:
        est = estimate_density_sampling(
            blocks, n0, n_max, m_list[n_max + 1], samples, seed
        )
        print(
            f"Sampled density over [0, M_{n_max + 1}] with {samples} samples: {est:.6f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Numerical checks for the doubling-ratio sequence construction."
    )
    parser.add_argument("--n-max", type=int, default=2, help="Largest block index N.")
    parser.add_argument("--n0", type=int, default=1, help="Cofinite start index n0.")
    parser.add_argument(
        "--max-m",
        type=int,
        default=None,
        help="Optional cap for m (defaults to M_{N+1}).",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=0,
        help="Random samples for density estimation over [0, M_{N+1}].",
    )
    parser.add_argument("--seed", type=int, default=0, help="RNG seed.")
    args = parser.parse_args()
    if args.n0 > args.n_max:
        raise SystemExit("n0 must be <= n-max")
    run(args.n_max, args.n0, args.max_m, args.samples, args.seed)


if __name__ == "__main__":
    main()
