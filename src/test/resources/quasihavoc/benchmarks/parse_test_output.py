#! /usr/bin/python3

import xml.etree.ElementTree as ET
from pathlib import Path
import re
import matplotlib.pyplot as plt

script_file = Path(__file__).resolve()
# we are currently in silicon/src/test/resources/quasihavoc/benchmarks
top_dir = script_file.parent.parent.parent.parent.parent.parent
xml_file = top_dir / 'target' / 'test-reports' / 'TEST-viper.silicon.tests.SiliconTests.xml'

tree = ET.parse(xml_file)
root = tree.getroot()

all_tests = {}

for testcase in root.iter('testcase'):
    name_str = testcase.get('name')
    time_str = testcase.get('time')

    match = re.match('quasihavoc/benchmarks/autogen/([\w]*)_(quasihavoc|alt)_([0-9]*)\.vpr', name_str)
    test_name, test_type, test_size = match.groups()
    test_size = int(test_size)

    if test_name not in all_tests:
        all_tests[test_name] = {}
        all_tests[test_name]['quasihavoc'] = []
        all_tests[test_name]['alt'] = []
    
    all_tests[test_name][test_type] += [(test_size, float(time_str))]

fig, axs = plt.subplots(nrows=(len(all_tests) + 1)//2, ncols=1)

handles = []

for i, test_name in enumerate(all_tests):
    ax = axs
    # ax = axs[i // 2, i % 2]
    data_havoc = sorted(all_tests[test_name]['quasihavoc'])[5:]
    data_alt = sorted(all_tests[test_name]['alt'])[5:]

    xs_havoc, ys_havoc = zip(*data_havoc)
    xs_alt, ys_alt = zip(*data_alt)

    line_havoc, = ax.plot(xs_havoc, ys_havoc, 'go--', label='quasihavoc')
    line_alt, = ax.plot(xs_alt, ys_alt, 'ro--', label='exhale inhale')

    ax.legend(handles=[line_alt, line_havoc])
    ax.set_title("Exhale/Inhale vs Havoc")
    ax.set_ylabel("Seconds")
    ax.set_xlabel("n")

plt.show()


