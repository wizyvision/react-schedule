import React, { memo } from "react"
import { useDrag } from 'react-dnd'

const EventItem = memo(function Event({ appointment, isDropped}) {
  const [{opacity}, drag] = useDrag(() => ({
      type: 'APPOINTMENT',
      item: { appointment},
      collect: (monitor) => ({
          opacity: monitor.isDragging() ? 0.4 : 1
      })
  }), [appointment])

  return (
      <div ref={drag} style={{ opacity, padding: '12px 8px', backgroundColor: 'peachpuff' }}>
          {isDropped ? <s>{appointment.title}</s> : appointment.title}
      </div>
  )
})

export default EventItem