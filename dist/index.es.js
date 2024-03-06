import React, { createContext, useContext } from 'react';

const SchedulerContext = /*#__PURE__*/createContext();
const SchedulerProvider = props => {
  const {
    children,
    color
  } = props;
  const value = {
    color
  };
  return /*#__PURE__*/React.createElement(SchedulerContext.Provider, {
    value: value
  }, children);
};
const useSchedulerContext = () => useContext(SchedulerContext);

function Calendar() {
  const {
    color
  } = useSchedulerContext();
  return /*#__PURE__*/React.createElement("div", null, color);
}

const Scheduler = props => {
  return /*#__PURE__*/React.createElement(SchedulerProvider, props, /*#__PURE__*/React.createElement("div", null, "Hello world"), /*#__PURE__*/React.createElement(Calendar, null));
};

export { Scheduler };
