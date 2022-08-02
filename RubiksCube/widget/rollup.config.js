import { nodeResolve } from '@rollup/plugin-node-resolve'
import typescript from '@rollup/plugin-typescript'
import commonjs from '@rollup/plugin-commonjs'
import replace from '@rollup/plugin-replace'

export default cliArgs => {
    const tsxName = cliArgs.tsxName
    if (tsxName === undefined)
        throw new Error("Please specify the .tsx to build with --tsxName <name>.")
    // We delete the custom argument so that Rollup does not try to process it and complain.
    delete cliArgs.tsxName

    return {
    input: [
        `src/${tsxName}.tsx`
    ],
    output: {
        dir: "dist",
        format: "es",
        // Hax: apparently setting `global` makes some CommonJS modules work ¯\_(ツ)_/¯
        intro: "const global = window"
    },
    external: [
        'react',
        'react-dom',
        '@leanprover/infoview',
    ],
    plugins: [
        typescript({
            tsconfig: "./tsconfig.json",
            outputToFilesystem: false,
            sourceMap: false
        }),
        nodeResolve({
            browser: true
        }),
        replace({
            'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV),
            preventAssignment: true // TODO delete when `true` becomes the default
        }),
        commonjs(),
    ]
}}
