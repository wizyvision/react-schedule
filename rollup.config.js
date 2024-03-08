import PeerDepsExternalPlugin from 'rollup-plugin-peer-deps-external';
import babel from '@rollup/plugin-babel';
const resolve = require('@rollup/plugin-node-resolve');
const commonjs = require('@rollup/plugin-commonjs');

// eslint-disable-next-line import/no-anonymous-default-export
module.exports = [
  {
    input: './src/index.js',
    output: [
      {
        file: 'dist/index.js',
        format: 'cjs',
      },
      {
        file: 'dist/index.es.js',
        format: 'es',
        exports: 'named',
      },
    ],
    plugins: [
      babel({
        exclude: 'node_modules/**',
        presets: ['@babel/preset-react', '@babel/preset-env'],
        babelHelpers: 'runtime',
        plugins: ['@babel/plugin-transform-runtime'],
      }),
      PeerDepsExternalPlugin(),
      resolve(),
      commonjs(),
    ],
    extensions: ['.js', '.jsx']
  },
];
