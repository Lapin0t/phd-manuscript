#page(
  numbering: none, margin: (y: 6cm), {
    set text(font: "Latin Modern Sans")

    align(center, [
        #let v-skip = v(1em, weak: true)
        #let v-space = v(2em, weak: true)

        #text(size: 18pt)[
          TITLE
        ]

        #v-space

        #text(fill: gray)[
          THIS IS A TEMPORARY TITLE PAGE
        ]

        #v-space
    ])
  },
)
