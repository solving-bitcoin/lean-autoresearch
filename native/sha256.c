#ifndef LEAN_USE_GMP
#define LEAN_USE_GMP 1
#endif
#include <lean/lean.h>
#include <lean/lean_gmp.h>
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

/*
 * Portable SHA-256/HMAC-SHA256 backend for the protected executable. This file
 * is deliberately outside the Lean privacy theorem. Native vectors check the
 * hash, PRF encoding, block-count transitions, and exact rejection sampler.
 */

typedef struct {
  uint32_t h[8];
  uint64_t byte_count;
  uint8_t block[64];
  size_t block_len;
} sha256_ctx;

static const uint32_t round_constants[64] = {
  0x428a2f98U, 0x71374491U, 0xb5c0fbcfU, 0xe9b5dba5U,
  0x3956c25bU, 0x59f111f1U, 0x923f82a4U, 0xab1c5ed5U,
  0xd807aa98U, 0x12835b01U, 0x243185beU, 0x550c7dc3U,
  0x72be5d74U, 0x80deb1feU, 0x9bdc06a7U, 0xc19bf174U,
  0xe49b69c1U, 0xefbe4786U, 0x0fc19dc6U, 0x240ca1ccU,
  0x2de92c6fU, 0x4a7484aaU, 0x5cb0a9dcU, 0x76f988daU,
  0x983e5152U, 0xa831c66dU, 0xb00327c8U, 0xbf597fc7U,
  0xc6e00bf3U, 0xd5a79147U, 0x06ca6351U, 0x14292967U,
  0x27b70a85U, 0x2e1b2138U, 0x4d2c6dfcU, 0x53380d13U,
  0x650a7354U, 0x766a0abbU, 0x81c2c92eU, 0x92722c85U,
  0xa2bfe8a1U, 0xa81a664bU, 0xc24b8b70U, 0xc76c51a3U,
  0xd192e819U, 0xd6990624U, 0xf40e3585U, 0x106aa070U,
  0x19a4c116U, 0x1e376c08U, 0x2748774cU, 0x34b0bcb5U,
  0x391c0cb3U, 0x4ed8aa4aU, 0x5b9cca4fU, 0x682e6ff3U,
  0x748f82eeU, 0x78a5636fU, 0x84c87814U, 0x8cc70208U,
  0x90befffaU, 0xa4506cebU, 0xbef9a3f7U, 0xc67178f2U
};

static inline uint32_t rotate_right(uint32_t x, unsigned n) {
  return (x >> n) | (x << (32U - n));
}

static uint32_t load_be32(const uint8_t *bytes) {
  return ((uint32_t)bytes[0] << 24) |
         ((uint32_t)bytes[1] << 16) |
         ((uint32_t)bytes[2] << 8) |
         (uint32_t)bytes[3];
}

static void store_be32(uint8_t *bytes, uint32_t value) {
  bytes[0] = (uint8_t)(value >> 24);
  bytes[1] = (uint8_t)(value >> 16);
  bytes[2] = (uint8_t)(value >> 8);
  bytes[3] = (uint8_t)value;
}

static void sha256_compress(sha256_ctx *ctx, const uint8_t block[64]) {
  uint32_t words[64];
  for (size_t i = 0; i < 16; ++i) {
    words[i] = load_be32(block + 4 * i);
  }
  for (size_t i = 16; i < 64; ++i) {
    uint32_t x = words[i - 15];
    uint32_t y = words[i - 2];
    uint32_t s0 = rotate_right(x, 7) ^ rotate_right(x, 18) ^ (x >> 3);
    uint32_t s1 = rotate_right(y, 17) ^ rotate_right(y, 19) ^ (y >> 10);
    words[i] = words[i - 16] + s0 + words[i - 7] + s1;
  }

  uint32_t a = ctx->h[0];
  uint32_t b = ctx->h[1];
  uint32_t c = ctx->h[2];
  uint32_t d = ctx->h[3];
  uint32_t e = ctx->h[4];
  uint32_t f = ctx->h[5];
  uint32_t g = ctx->h[6];
  uint32_t h = ctx->h[7];

  for (size_t i = 0; i < 64; ++i) {
    uint32_t s1 = rotate_right(e, 6) ^ rotate_right(e, 11) ^ rotate_right(e, 25);
    uint32_t choose = (e & f) ^ ((~e) & g);
    uint32_t t1 = h + s1 + choose + round_constants[i] + words[i];
    uint32_t s0 = rotate_right(a, 2) ^ rotate_right(a, 13) ^ rotate_right(a, 22);
    uint32_t majority = (a & b) ^ (a & c) ^ (b & c);
    uint32_t t2 = s0 + majority;
    h = g;
    g = f;
    f = e;
    e = d + t1;
    d = c;
    c = b;
    b = a;
    a = t1 + t2;
  }

  ctx->h[0] += a;
  ctx->h[1] += b;
  ctx->h[2] += c;
  ctx->h[3] += d;
  ctx->h[4] += e;
  ctx->h[5] += f;
  ctx->h[6] += g;
  ctx->h[7] += h;
}

static void sha256_init(sha256_ctx *ctx) {
  static const uint32_t initial[8] = {
    0x6a09e667U, 0xbb67ae85U, 0x3c6ef372U, 0xa54ff53aU,
    0x510e527fU, 0x9b05688cU, 0x1f83d9abU, 0x5be0cd19U
  };
  memcpy(ctx->h, initial, sizeof(initial));
  ctx->byte_count = 0;
  ctx->block_len = 0;
}

static void sha256_update(sha256_ctx *ctx, const uint8_t *input, size_t length) {
  ctx->byte_count += (uint64_t)length;
  while (length > 0) {
    size_t available = 64 - ctx->block_len;
    size_t take = length < available ? length : available;
    memcpy(ctx->block + ctx->block_len, input, take);
    ctx->block_len += take;
    input += take;
    length -= take;
    if (ctx->block_len == 64) {
      sha256_compress(ctx, ctx->block);
      ctx->block_len = 0;
    }
  }
}

static void sha256_final(sha256_ctx *ctx, uint8_t digest[32]) {
  uint64_t bit_count = ctx->byte_count * 8U;
  ctx->block[ctx->block_len++] = 0x80U;
  if (ctx->block_len > 56) {
    memset(ctx->block + ctx->block_len, 0, 64 - ctx->block_len);
    sha256_compress(ctx, ctx->block);
    ctx->block_len = 0;
  }
  memset(ctx->block + ctx->block_len, 0, 56 - ctx->block_len);
  for (size_t i = 0; i < 8; ++i) {
    ctx->block[63 - i] = (uint8_t)(bit_count >> (8 * i));
  }
  sha256_compress(ctx, ctx->block);
  for (size_t i = 0; i < 8; ++i) {
    store_be32(digest + 4 * i, ctx->h[i]);
  }
}

typedef struct {
  sha256_ctx inner;
  sha256_ctx outer;
} hmac_sha256_state;

static void hmac_sha256_prepare(const uint8_t *key, size_t key_len,
                                hmac_sha256_state *state) {
  uint8_t key_block[64] = {0};
  uint8_t inner_pad[64];
  uint8_t outer_pad[64];
  if (key_len > 64) {
    sha256_ctx key_ctx;
    sha256_init(&key_ctx);
    sha256_update(&key_ctx, key, key_len);
    sha256_final(&key_ctx, key_block);
  } else {
    memcpy(key_block, key, key_len);
  }
  for (size_t i = 0; i < 64; ++i) {
    inner_pad[i] = (uint8_t)(key_block[i] ^ 0x36U);
    outer_pad[i] = (uint8_t)(key_block[i] ^ 0x5cU);
  }
  sha256_init(&state->inner);
  sha256_update(&state->inner, inner_pad, sizeof(inner_pad));
  sha256_init(&state->outer);
  sha256_update(&state->outer, outer_pad, sizeof(outer_pad));
}

static void hmac_sha256_from_state(const hmac_sha256_state *state,
                                   const uint8_t *input, size_t input_len,
                                   uint8_t digest[32]) {
  uint8_t inner_digest[32];
  sha256_ctx inner = state->inner;
  sha256_update(&inner, input, input_len);
  sha256_final(&inner, inner_digest);

  sha256_ctx outer = state->outer;
  sha256_update(&outer, inner_digest, sizeof(inner_digest));
  sha256_final(&outer, digest);
}

/* A run uses one internal-oracle key and one independent test-label key for
 * hundreds of thousands of HMACs. Cache only the two exact 32-byte key
 * schedules per thread. This changes no HMAC bytes, avoids shared mutable
 * state between evaluator threads, and bounds retained key material. */
typedef struct {
  int valid;
  uint8_t key[32];
  hmac_sha256_state state;
} hmac_sha256_cache_entry;

static _Thread_local hmac_sha256_cache_entry hmac_sha256_cache[2];
static _Thread_local unsigned hmac_sha256_cache_next;

static const hmac_sha256_state *hmac_sha256_cached_state(
    const uint8_t key[32]) {
  for (size_t i = 0; i < 2; ++i) {
    if (hmac_sha256_cache[i].valid &&
        memcmp(hmac_sha256_cache[i].key, key, 32) == 0) {
      return &hmac_sha256_cache[i].state;
    }
  }
  hmac_sha256_cache_entry *entry =
    &hmac_sha256_cache[hmac_sha256_cache_next++ % 2];
  memcpy(entry->key, key, 32);
  hmac_sha256_prepare(key, 32, &entry->state);
  entry->valid = 1;
  return &entry->state;
}

static void hmac_sha256(const uint8_t *key, size_t key_len,
                        const uint8_t *input, size_t input_len,
                        uint8_t digest[32]) {
  if (key_len == 32) {
    hmac_sha256_from_state(hmac_sha256_cached_state(key), input, input_len,
                           digest);
  } else {
    hmac_sha256_state state;
    hmac_sha256_prepare(key, key_len, &state);
    hmac_sha256_from_state(&state, input, input_len, digest);
  }
}

static size_t trim_le(const uint8_t *value, size_t length) {
  while (length > 0 && value[length - 1] == 0) {
    --length;
  }
  return length;
}

/* Match SeededInternalOracle.encodeNat for a little-endian byte sequence. */
static size_t encode_nat_marked(const uint8_t *digits, size_t length,
                                uint8_t *output) {
  length = trim_le(digits, length);
  size_t cursor = 0;
  for (size_t i = 0; i < length; ++i) {
    output[cursor++] = 1;
    output[cursor++] = digits[i];
  }
  output[cursor++] = 0;
  return cursor;
}

static unsigned byte_bit_length(uint8_t value) {
  unsigned result = 0;
  while (value != 0) {
    ++result;
    value >>= 1;
  }
  return result;
}

static int is_power_of_two_le(const uint8_t *value, size_t length) {
  unsigned seen = 0;
  for (size_t i = 0; i < length; ++i) {
    uint8_t byte = value[i];
    while (byte != 0) {
      seen += byte & 1U;
      if (seen > 1) {
        return 0;
      }
      byte >>= 1;
    }
  }
  return seen == 1;
}

static int compare_le(const uint8_t *left, const uint8_t *right,
                      size_t length) {
  for (size_t i = length; i-- > 0;) {
    if (left[i] < right[i]) {
      return -1;
    }
    if (left[i] > right[i]) {
      return 1;
    }
  }
  return 0;
}

static void subtract_le(uint8_t *left, const uint8_t *right, size_t length) {
  unsigned borrow = 0;
  for (size_t i = 0; i < length; ++i) {
    unsigned subtrahend = (unsigned)right[i] + borrow;
    unsigned current = left[i];
    left[i] = (uint8_t)(current - subtrahend);
    borrow = current < subtrahend;
  }
}

/* Replace remainder by (2 * remainder + bit) mod modulus. */
static void remainder_step(uint8_t *remainder, const uint8_t *modulus,
                           size_t length, unsigned bit) {
  unsigned carry = bit;
  for (size_t i = 0; i < length; ++i) {
    unsigned next = ((unsigned)remainder[i] << 1) | carry;
    remainder[i] = (uint8_t)next;
    carry = next >> 8;
  }
  if (carry != 0 || compare_le(remainder, modulus, length) >= 0) {
    subtract_le(remainder, modulus, length);
  }
}

static void power_of_two_remainder(uint8_t *remainder,
                                   const uint8_t *modulus,
                                   size_t length, size_t exponent) {
  /* If the modulus occupies the full candidate byte width, then
   * 2^(8*length) / modulus is at most 256.  Extended-width subtraction avoids
   * repeating the generic bitwise reduction for every BN254 oracle query. */
  if (exponent == 8 * length && trim_le(modulus, length) == length) {
    uint8_t extended[385] = {0};
    uint8_t extended_modulus[385] = {0};
    memcpy(extended_modulus, modulus, length);
    extended[length] = 1;
    while (compare_le(extended, extended_modulus, length + 1) >= 0) {
      subtract_le(extended, extended_modulus, length + 1);
    }
    memcpy(remainder, extended, length);
    return;
  }
  memset(remainder, 0, length);
  if (length == 1 && modulus[0] == 1) {
    return;
  }
  remainder[0] = 1;
  for (size_t i = 0; i < exponent; ++i) {
    remainder_step(remainder, modulus, length, 0);
  }
}

static int add_overflows(const uint8_t *left, const uint8_t *right,
                         size_t length) {
  unsigned carry = 0;
  for (size_t i = 0; i < length; ++i) {
    unsigned sum = (unsigned)left[i] + (unsigned)right[i] + carry;
    carry = sum >> 8;
  }
  return carry != 0;
}

static void reduce_modulus(uint8_t *result, const uint8_t *candidate,
                           const uint8_t *modulus, size_t length) {
  /* The official BN254 moduli occupy the candidate's full byte width.  In
   * that case the quotient is below 256, and repeated exact subtraction is
   * substantially faster than bitwise long division across ~450k samples. */
  if (trim_le(modulus, length) == length) {
    memcpy(result, candidate, length);
    while (compare_le(result, modulus, length) >= 0) {
      subtract_le(result, modulus, length);
    }
    return;
  }
  memset(result, 0, length);
  for (size_t bit = 8 * length; bit-- > 0;) {
    unsigned selected =
      ((unsigned)candidate[bit / 8] >> (bit % 8)) & 1U;
    remainder_step(result, modulus, length, selected);
  }
}

static int increment_digits(uint8_t **digits, size_t *length) {
  if (*length == 0) {
    *digits = (uint8_t *)malloc(1);
    if (*digits == NULL) {
      return 0;
    }
    (*digits)[0] = 1;
    *length = 1;
    return 1;
  }
  size_t i = 0;
  while (i < *length && (*digits)[i] == 0xffU) {
    (*digits)[i] = 0;
    ++i;
  }
  if (i < *length) {
    ++(*digits)[i];
    return 1;
  }
  uint8_t *grown = (uint8_t *)realloc(*digits, *length + 1);
  if (grown == NULL) {
    return 0;
  }
  grown[*length] = 1;
  *digits = grown;
  ++*length;
  return 1;
}

LEAN_EXPORT lean_obj_res lean_g1_hmac_sha256(lean_obj_arg key,
                                              lean_obj_arg input) {
  uint8_t digest[32];
  hmac_sha256(lean_sarray_cptr(key), lean_sarray_size(key),
              lean_sarray_cptr(input), lean_sarray_size(input), digest);
  lean_dec(key);
  lean_dec(input);
  lean_object *output = lean_alloc_sarray(1, 32, 32);
  memcpy(lean_sarray_cptr(output), digest, 32);
  return output;
}

static lean_obj_res uniform_below_borrowed(b_lean_obj_arg seed,
                                           b_lean_obj_arg modulus_input,
                                           b_lean_obj_arg purpose) {
  static const uint8_t domain[] =
    "g1-q-plus-rA/internal-uniform/v1";

  if (lean_sarray_size(seed) != 32 || lean_sarray_size(modulus_input) != 385) {
    return lean_alloc_sarray(1, 0, 0);
  }
  const uint8_t *modulus_full = lean_sarray_cptr(modulus_input);
  size_t modulus_length = trim_le(modulus_full, 385);
  if (modulus_length == 0) {
    return lean_alloc_sarray(1, 0, 0);
  }

  size_t bit_length = 8 * (modulus_length - 1) +
    byte_bit_length(modulus_full[modulus_length - 1]);
  size_t width = bit_length - (is_power_of_two_le(modulus_full,
    modulus_length) ? 1U : 0U);
  size_t blocks = (width + 255U) / 256U;
  if (blocks == 0) {
    blocks = 1;
  }
  if (blocks > 12) {
    return lean_alloc_sarray(1, 0, 0);
  }
  size_t candidate_length = blocks * 32;

  int modulus_is_range = modulus_length == candidate_length + 1 &&
    modulus_full[candidate_length] == 1;
  if (modulus_is_range) {
    for (size_t i = 0; i < candidate_length; ++i) {
      if (modulus_full[i] != 0) {
        modulus_is_range = 0;
        break;
      }
    }
  }
  if (!modulus_is_range && modulus_length > candidate_length) {
    return lean_alloc_sarray(1, 0, 0);
  }

  uint8_t modulus[384] = {0};
  uint8_t rejection_tail[384] = {0};
  uint8_t candidate[384] = {0};
  uint8_t reduced[384] = {0};
  if (!modulus_is_range) {
    memcpy(modulus, modulus_full, modulus_length);
    power_of_two_remainder(rejection_tail, modulus, candidate_length,
                           8 * candidate_length);
  }

  uint8_t modulus_encoded[771];
  size_t modulus_encoded_length = encode_nat_marked(
    modulus_full, modulus_length, modulus_encoded);
  uint8_t *attempt_digits = NULL;
  size_t attempt_length = 0;

  for (;;) {
    size_t attempt_encoded_length = 2 * attempt_length + 1;
    uint8_t *attempt_encoded =
      (uint8_t *)malloc(attempt_encoded_length);
    if (attempt_encoded == NULL) {
      free(attempt_digits);
      return lean_alloc_sarray(1, 0, 0);
    }
    encode_nat_marked(attempt_digits, attempt_length, attempt_encoded);

    for (size_t block = 0; block < blocks; ++block) {
      uint8_t block_digit = (uint8_t)block;
      uint8_t block_encoded[3];
      size_t block_encoded_length = encode_nat_marked(
        &block_digit, block == 0 ? 0 : 1, block_encoded);
      size_t message_length = (sizeof(domain) - 1) + modulus_encoded_length +
        lean_sarray_size(purpose) + attempt_encoded_length +
        block_encoded_length;
      uint8_t *message = (uint8_t *)malloc(message_length);
      if (message == NULL) {
        free(attempt_encoded);
        free(attempt_digits);
        return lean_alloc_sarray(1, 0, 0);
      }
      size_t cursor = 0;
      memcpy(message + cursor, domain, sizeof(domain) - 1);
      cursor += sizeof(domain) - 1;
      memcpy(message + cursor, modulus_encoded, modulus_encoded_length);
      cursor += modulus_encoded_length;
      memcpy(message + cursor, lean_sarray_cptr(purpose),
             lean_sarray_size(purpose));
      cursor += lean_sarray_size(purpose);
      memcpy(message + cursor, attempt_encoded, attempt_encoded_length);
      cursor += attempt_encoded_length;
      memcpy(message + cursor, block_encoded, block_encoded_length);

      uint8_t digest[32];
      hmac_sha256(lean_sarray_cptr(seed), 32, message, message_length, digest);
      free(message);
      for (size_t byte = 0; byte < 32; ++byte) {
        size_t big_endian_index = block * 32 + byte;
        candidate[candidate_length - 1 - big_endian_index] = digest[byte];
      }
    }
    free(attempt_encoded);

    int accepted = modulus_is_range ||
      !add_overflows(candidate, rejection_tail, candidate_length);
    if (accepted) {
      if (modulus_is_range) {
        memcpy(reduced, candidate, candidate_length);
      } else {
        reduce_modulus(reduced, candidate, modulus, candidate_length);
      }
      lean_object *output =
        lean_alloc_sarray(1, candidate_length, candidate_length);
      memcpy(lean_sarray_cptr(output), reduced, candidate_length);
      free(attempt_digits);
      return output;
    }
    if (!increment_digits(&attempt_digits, &attempt_length)) {
      free(attempt_digits);
      return lean_alloc_sarray(1, 0, 0);
    }
  }
}

LEAN_EXPORT lean_obj_res lean_g1_uniform_below(lean_obj_arg seed,
                                               lean_obj_arg modulus_input,
                                               lean_obj_arg purpose) {
  lean_object *result =
    uniform_below_borrowed(seed, modulus_input, purpose);
  lean_dec(seed);
  lean_dec(modulus_input);
  lean_dec(purpose);
  return result;
}

/* Convert the exact sampler output directly to Lean's natural-number
 * representation.  This avoids reconstructing a 256--3072-bit value through
 * one Lean big-natural addition per byte. */
LEAN_EXPORT lean_obj_res lean_g1_uniform_below_nat(lean_obj_arg seed,
                                                   lean_obj_arg modulus_input,
                                                   lean_obj_arg purpose) {
  lean_object *bytes =
    lean_g1_uniform_below(seed, modulus_input, purpose);
  size_t length = lean_sarray_size(bytes);
  if (length == 0 || length > 384 || length % 32 != 0) {
    lean_dec(bytes);
    return lean_box(0);
  }

  mpz_t value;
  mpz_init(value);
  mpz_import(value, length, -1, 1, 0, 0, lean_sarray_cptr(bytes));
  lean_dec(bytes);

  lean_object *natural;
  if (mpz_fits_ulong_p(value) && mpz_get_ui(value) <= LEAN_MAX_SMALL_NAT) {
    natural = lean_box((size_t)mpz_get_ui(value));
  } else {
    natural = lean_alloc_mpz(value);
  }
  mpz_clear(value);

  lean_object *result = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(result, 0, natural);
  return result;
}

/* Exact 32-byte little-endian natural encoding used for BN254 field words.
 * `Codec.natLE32` has the original transparent Lean body, so this is only a
 * compiled specialization of the proved codec. */
LEAN_EXPORT lean_obj_res lean_g1_nat_le_32(lean_obj_arg value) {
  uint8_t bytes[32];
  memset(bytes, 0, 32);

  if (lean_is_scalar(value)) {
    size_t word = lean_unbox(value);
    for (size_t i = 0; i < sizeof(size_t) && i < 32; ++i) {
      bytes[i] = (uint8_t)(word >> (8 * i));
    }
  } else if (lean_is_mpz(value)) {
    mpz_t natural;
    size_t written = 0;
    mpz_init(natural);
    lean_extract_mpz_value((lean_object *)value, natural);
    mpz_export(bytes, &written, -1, 1, 0, 0, natural);
    mpz_clear(natural);
  }
  lean_dec(value);

  /* `Bytes 32` erases to `Array UInt8`, not `ByteArray`.  Populate the
   * boxed-array representation expected by `Vector`; returning a scalar
   * array here corrupts the ABI even though both hold byte-sized values. */
  lean_object *output = lean_alloc_array(32, 32);
  for (size_t i = 0; i < 32; ++i) {
    lean_array_set_core(output, i, lean_box(bytes[i]));
  }
  return output;
}

/* Pack the four low 254-bit prefixes into one dense 1016-bit boxed byte
 * array.  Inputs and output use Lean's `Array UInt8` representation because
 * the corresponding types are `Vector`, not `ByteArray`. */
LEAN_EXPORT lean_obj_res lean_g1_pack_four_254(lean_obj_arg words) {
  uint8_t packed_bytes[127] = {0};

  /* The four 254-bit words begin at bit offsets 0, 254, 508, and 762.
   * Copy whole source bytes and handle only the sub-byte displacement between
   * adjacent words.  Masking byte 31 discards the two unused high bits. */
  for (size_t slot = 0; slot < 4; ++slot) {
    lean_object *word = lean_array_get_core(words, slot);
    for (size_t byte = 0; byte < 32; ++byte) {
      uint8_t source = (uint8_t)lean_unbox(lean_array_get_core(word, byte));
      if (byte == 31) {
        source &= 0x3fU;
      }
      size_t bit_offset = slot * 254 + byte * 8;
      size_t output_index = bit_offset / 8;
      size_t shift = bit_offset % 8;
      packed_bytes[output_index] |= (uint8_t)(source << shift);
      if (shift != 0 && output_index + 1 < 127) {
        packed_bytes[output_index + 1] |=
          (uint8_t)(source >> (8 - shift));
      }
    }
  }

  lean_object *output = lean_alloc_array(127, 127);
  for (size_t byte = 0; byte < 127; ++byte) {
    lean_array_set_core(output, byte, lean_box(packed_bytes[byte]));
  }
  lean_dec(words);
  return output;
}

LEAN_EXPORT lean_obj_res lean_g1_sha256(lean_obj_arg input) {
  sha256_ctx ctx;
  uint8_t digest[32];
  sha256_init(&ctx);
  sha256_update(&ctx, lean_sarray_cptr(input), lean_sarray_size(input));
  sha256_final(&ctx, digest);
  lean_dec_ref(input);
  lean_object *output = lean_alloc_sarray(1, 32, 32);
  memcpy(lean_sarray_cptr(output), digest, 32);
  return output;
}
