import React from 'react'
import { useSchedulerContext } from '../Scheduler/SchedulerProvider'

function Calendar() {
  const {color} = useSchedulerContext()
  return (
    <div>{color}</div>
  )
}

export default Calendar