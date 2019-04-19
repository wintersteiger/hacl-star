import re
import json
import itertools
from os import listdir

regex_rsp_l = r'\[L = (?P<md_len>\d+)\]\s+'
regex_rsp_len = r'Len = (?P<len>\w+)\s+'
regex_rsp_msg = r'Msg = (?P<msg>\w+)\s+'
regex_rsp_md = r'MD = (?P<md>\w+)\s+'

test_no = 0

def parse_rsp(suite_name, f):
    tests = []
    global test_no
    for _, g in itertools.groupby(list(f), (lambda l: l == '\n')):
        g = list(g)
        if g != ['\n']:
            tests.append(g)
    tests = tests[1:] # discard initial comments
    md_len = re.search(regex_rsp_l, tests[0][0]).group('md_len')

    vectors = []
    for v in tests[1:]:
        test_len = re.search(regex_rsp_len, v[0]).group('len')
        test_msg = re.search(regex_rsp_msg, v[1]).group('msg')
        test_md = re.search(regex_rsp_md, v[2]).group('md')
        if int(test_len) == 0:
            test_msg = ''
        vectors.append({'test_no': int(test_no), 'input_len': int(test_len), 'input': test_msg, 'output_len': int(md_len), 'output': test_md})
        test_no += 1
    return vectors

def main():
    path = 'fips-202'
    files = listdir(path)
    suites = []
    for rsp in files:
        assert (rsp[-4:] == '.rsp')
        suite_name = rsp[:-4]
        with open(path + '/' + rsp, 'r') as f:
            suites += parse_rsp(suite_name, f)
    with open('generated/json/' + path + '-sha3_test.json', 'w') as f:
         json.dump(suites, f, indent=2, separators=(',', ': '))


main ()
