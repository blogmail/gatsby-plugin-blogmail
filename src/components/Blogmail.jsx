import BM from "@blogmail/react"
import PropTypes from "prop-types"
import React from "react"

// function isReactElement(element) {
//   if (React.isValidElement(element)) {
//     return true
//   } else if (Array.isArray(element)) {
//     return element.some((value) => React.isValidElement(value))
//   }
//   return false
// }

// function shallowComparison(currentProps, nextProps) {
//   // Perform a comparison of all props, excluding React Elements, to prevent unnecessary updates
//   const propNames = new Set(
//     Object.keys(currentProps).concat(Object.keys(nextProps))
//   )
//   const changes = []
//     .concat(...propNames)
//     .filter(
//       (name) =>
//         currentProps[name] !== nextProps[name] &&
//         !isReactElement(currentProps[name])
//     )
//   return changes.length !== 0
// }

export default class Blogmail extends React.Component {
  constructor(props) {
    super(props)
    this.newsletterId =
      typeof GATSBY_BLOGMAIL_NEWSLETTERID !== `undefined` &&
      GATSBY_BLOGMAIL_NEWSLETTERID !== ""
        ? GATSBY_BLOGMAIL_NEWSLETTERID
        : ""
  }

  // componentDidMount() {
  //   if (typeof window !== "undefined" && this.newsletterId) {
  //     this.cleanInstance()
  //   }
  //   this.loadInstance()
  // }

  // shouldComponentUpdate(nextProps) {
  //   if (this.props === nextProps) {
  //     return false
  //   }
  //   return shallowComparison(this.props, nextProps)
  // }

  // getblogmailConfig(config) {
  //   return function () {}
  // }

  // cleanInstance() {
  //   try {
  //     delete window.Blogmail
  //   } catch (error) {
  //     window.Blogmail = undefined
  //   }
  // }

  render = () => {
    let { config, ...props } = this.props
    return <BM {...props} newsletterId={this.newsletterId} />
  }
}

// Blogmail.propTypes = {
//   config: PropTypes.shape({
//     /*
//      * Tells the blogmail service how to identify the current page.
//      * When the blogmail embed is loaded, the identifier is used to look up
//      * the correct thread.
//      */
//     identifier: PropTypes.string,
//     /*
//      * Tells the blogmail service the title of the current page.
//      * This is used when creating the thread on blogmail.
//      */
//     title: PropTypes.string,
//     /*
//      * Tells the blogmail service the URL of the current page.
//      * This URL is used when a thread is created so that blogmail knows which
//      * page a thread belongs to.
//      * (If undefined, blogmail will use the global.location.href)
//      */
//     url: PropTypes.string,
//     /*
//      * Tells the blogmail service to override the default site language for the
//      * current page.
//      * This allows for dynamically loading the blogmail embed in different
//      * languages on a per-page basis.
//      * (If undefined, blogmail will use the default site language)
//      */
//     language: PropTypes.string,
//     /*
//       The generated payload used to pass Single Sign-On (SSO) user data
//      */
//     remoteAuthS3: PropTypes.string,
//     /*
//      * This is the public API key for your Single Sign-On (SSO) integration
//      */
//     apiKey: PropTypes.string,
//   }),
// }
