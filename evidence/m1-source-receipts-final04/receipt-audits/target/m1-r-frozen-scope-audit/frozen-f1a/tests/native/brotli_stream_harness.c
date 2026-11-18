/* Test-only streaming harness for pinned native Brotli references.
 *
 * This program is not linked into the Rust library or its proof model.
 */

#include <brotli/decode.h>

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { GUARD = 32 };

static int nibble(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static int parse_size(const char* text, size_t* value) {
  char* end = NULL;
  uintmax_t parsed;
  errno = 0;
  parsed = strtoumax(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || parsed > SIZE_MAX) return 0;
  *value = (size_t)parsed;
  return 1;
}

static int guards_intact(const uint8_t* allocation, size_t capacity) {
  size_t i;
  for (i = 0; i < GUARD; ++i) {
    if (allocation[i] != 0xA5) return 0;
    if (allocation[GUARD + capacity + i] != 0x5A) return 0;
  }
  return 1;
}

static void print_hex(const uint8_t* bytes, size_t length) {
  static const char digits[] = "0123456789abcdef";
  size_t i;
  for (i = 0; i < length; ++i) {
    putchar(digits[bytes[i] >> 4]);
    putchar(digits[bytes[i] & 15]);
  }
}

static uint64_t fnv1a64(const uint8_t* bytes, size_t length) {
  uint64_t hash = UINT64_C(14695981039346656037);
  size_t i;
  for (i = 0; i < length; ++i) {
    hash ^= bytes[i];
    hash *= UINT64_C(1099511628211);
  }
  return hash;
}

int main(int argc, char** argv) {
  const char* hex;
  size_t input_chunk;
  size_t output_chunk;
  size_t output_capacity;
  size_t max_steps;
  size_t input_length;
  uint8_t* input;
  uint8_t* allocation;
  uint8_t* output;
  BrotliDecoderState* state;
  BrotliDecoderResult result = BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT;
  BrotliDecoderErrorCode error = BROTLI_DECODER_NO_ERROR;
  size_t input_position = 0;
  size_t output_position = 0;
  size_t step = 0;
  int stalled = 0;
  int final_guards;
  FILE* output_file;

  if (argc != 7) {
    fprintf(stderr, "usage: %s HEX INPUT_CHUNK OUTPUT_CHUNK OUTPUT_CAP MAX_STEPS OUTPUT_FILE\n", argv[0]);
    return 64;
  }
  hex = argv[1];
  if (!parse_size(argv[2], &input_chunk) || input_chunk == 0 ||
      !parse_size(argv[3], &output_chunk) || output_chunk == 0 ||
      !parse_size(argv[4], &output_capacity) ||
      !parse_size(argv[5], &max_steps) || max_steps == 0) {
    fprintf(stderr, "invalid numeric argument\n");
    return 64;
  }
  if (output_capacity > SIZE_MAX - 2 * GUARD) {
    fprintf(stderr, "output capacity overflow\n");
    return 64;
  }
  if (strlen(hex) % 2 != 0) {
    fprintf(stderr, "odd hex length\n");
    return 64;
  }
  input_length = strlen(hex) / 2;
  input = (uint8_t*)malloc(input_length == 0 ? 1 : input_length);
  allocation = (uint8_t*)malloc(output_capacity + 2 * GUARD);
  if (input == NULL || allocation == NULL) {
    fprintf(stderr, "allocation failed\n");
    free(input);
    free(allocation);
    return 70;
  }
  for (size_t i = 0; i < input_length; ++i) {
    int high = nibble(hex[2 * i]);
    int low = nibble(hex[2 * i + 1]);
    if (high < 0 || low < 0) {
      fprintf(stderr, "invalid hex\n");
      free(input);
      free(allocation);
      return 64;
    }
    input[i] = (uint8_t)((high << 4) | low);
  }
  memset(allocation, 0xA5, GUARD);
  memset(allocation + GUARD, 0xCC, output_capacity);
  memset(allocation + GUARD + output_capacity, 0x5A, GUARD);
  output = allocation + GUARD;
  state = BrotliDecoderCreateInstance(NULL, NULL, NULL);
  if (state == NULL) {
    fprintf(stderr, "decoder creation failed\n");
    free(input);
    free(allocation);
    return 70;
  }

  while (step < max_steps) {
    size_t offered_in = input_length - input_position;
    size_t offered_out = output_capacity - output_position;
    const uint8_t* next_in;
    uint8_t* next_out;
    size_t available_in;
    size_t available_out;
    size_t total_out = output_position;
    size_t consumed;
    size_t produced;

    if (offered_in > input_chunk) offered_in = input_chunk;
    if (offered_out > output_chunk) offered_out = output_chunk;
    next_in = input + input_position;
    next_out = output + output_position;
    available_in = offered_in;
    available_out = offered_out;
    result = BrotliDecoderDecompressStream(
        state, &available_in, &next_in, &available_out, &next_out, &total_out);
    consumed = offered_in - available_in;
    produced = offered_out - available_out;
    input_position += consumed;
    output_position += produced;
    error = BrotliDecoderGetErrorCode(state);
    printf("step=%zu offered_in=%zu consumed=%zu produced=%zu result=%d error=%d\n",
           step, offered_in, consumed, produced, (int)result, (int)error);
    ++step;

    if (!guards_intact(allocation, output_capacity)) {
      fprintf(stderr, "guard corruption\n");
      BrotliDecoderDestroyInstance(state);
      free(input);
      free(allocation);
      return 90;
    }
    if (result == BROTLI_DECODER_RESULT_SUCCESS ||
        result == BROTLI_DECODER_RESULT_ERROR) {
      break;
    }
    if (result == BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT && offered_out == 0) {
      stalled = 1;
      break;
    }
    if (result == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT &&
        input_position == input_length && offered_in == 0) {
      stalled = 1;
      break;
    }
    if (consumed == 0 && produced == 0 && offered_in != 0 && offered_out != 0) {
      stalled = 1;
      break;
    }
  }

  output_file = fopen(argv[6], "wb");
  if (output_file == NULL || fwrite(output, 1, output_position, output_file) != output_position ||
      fclose(output_file) != 0) {
    fprintf(stderr, "could not write output file\n");
    BrotliDecoderDestroyInstance(state);
    free(input);
    free(allocation);
    return 74;
  }
  printf("summary result=%d error=%d consumed=%zu produced=%zu steps=%zu stalled=%d guards=%d fnv1a64=%016" PRIx64 " preview=",
         (int)result, (int)error, input_position, output_position, step, stalled,
         guards_intact(allocation, output_capacity), fnv1a64(output, output_position));
  print_hex(output, output_position < 64 ? output_position : 64);
  putchar('\n');

  final_guards = guards_intact(allocation, output_capacity);
  BrotliDecoderDestroyInstance(state);
  free(input);
  free(allocation);
  return final_guards ? 0 : 90;
}
