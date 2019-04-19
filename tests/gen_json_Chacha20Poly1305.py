import json


def main():
    with open('google-wycheproof/chacha20_poly1305_test.json', 'r') as f:
        tests = f.read()
    j = json.loads(tests)
    original_tests = j['testGroups'][0]['tests']
    vectors = []
    for t in original_tests:
        vectors.append(
            { 'test_no': t['tcId'],
              'key': t['key'],
              'nonce': t['iv'],
              'input': t['msg'],
              'output': t['ct'],
              'aad': t['aad'],
              'tag': t['tag']
            }
        )
    with open('generated/json/google-wycheproof-chacha20_poly1305_test.json', 'w') as f:
        json.dump(vectors, f, indent=2, separators=(',', ': '))

main ()
