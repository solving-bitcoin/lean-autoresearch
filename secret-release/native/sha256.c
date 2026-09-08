/* Portable SHA-256 extracted from ../native/sha256.c (same repository license).
 * This is a trusted runtime instantiation, outside the ideal-ROM theorem.
 * No HMAC, GMP, modulus sampler, or native arithmetic is linked here. */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>

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

LEAN_EXPORT lean_obj_res lean_secret_release_sha256(lean_obj_arg input) {
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
