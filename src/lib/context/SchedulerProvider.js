import React, { useContext, createContext } from 'react';

const SchedulerContext = createContext();

const SchedulerProvider = (props) => {
  const { children, color } = props;

  const value = {
    color,
  };

  return (
    <SchedulerContext.Provider value={value}>
      {children}
    </SchedulerContext.Provider>
  );
};

const useSchedulerContext = () => {
  return useContext(SchedulerContext);
};

export { SchedulerProvider, useSchedulerContext };
