import React from 'react'

import SchedulerDatePicker from './DatePicker'
import DurationPicker from './DurationPicker'
import NavigateDateAction from './NavigateDate'

function Header() {
    console.log('error')
  return (
    <div style={{display: 'flex', alignItems: 'center', justifyContent: 'space-between'}}  >
        <NavigateDateAction />
        <SchedulerDatePicker />
        <DurationPicker />
    </div>
  )
}

export default Header