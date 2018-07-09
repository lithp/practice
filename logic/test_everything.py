#!/usr/bin/env python3

import unittest

import logic
import pattern

if __name__ == '__main__':
    suite = unittest.TestSuite()

    for module in (logic, pattern):
        suite.addTest(
            unittest.defaultTestLoader.loadTestsFromModule(module)
        )

    runner = unittest.TextTestRunner()
    runner.run(suite)
